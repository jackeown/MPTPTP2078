%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:35 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   41 (  60 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  95 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_119,plain,(
    ! [A_34,B_35,C_36] :
      ( k9_subset_1(A_34,B_35,C_36) = k3_xboole_0(B_35,C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,(
    ! [B_35] : k9_subset_1('#skF_1',B_35,'#skF_3') = k3_xboole_0(B_35,'#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_119])).

tff(c_179,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k9_subset_1(A_39,B_40,C_41),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_192,plain,(
    ! [B_35] :
      ( m1_subset_1(k3_xboole_0(B_35,'#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_179])).

tff(c_199,plain,(
    ! [B_35] : m1_subset_1(k3_xboole_0(B_35,'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_192])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k3_subset_1(A_7,B_8),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_81,plain,(
    ! [A_30,B_31] :
      ( k3_subset_1(A_30,k3_subset_1(A_30,B_31)) = B_31
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_90,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_81])).

tff(c_222,plain,(
    ! [C_44,A_45,B_46] :
      ( r1_tarski(C_44,k3_subset_1(A_45,B_46))
      | ~ r1_tarski(B_46,k3_subset_1(A_45,C_44))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_224,plain,(
    ! [B_46] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',B_46))
      | ~ r1_tarski(B_46,'#skF_2')
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_46,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_222])).

tff(c_284,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_287,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_284])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_287])).

tff(c_795,plain,(
    ! [B_74] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',B_74))
      | ~ r1_tarski(B_74,'#skF_2')
      | ~ m1_subset_1(B_74,k1_zfmisc_1('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_18,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k9_subset_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_129,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_18])).

tff(c_800,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_795,c_129])).

tff(c_823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_2,c_800])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.41  
% 2.82/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.41  %$ r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.82/1.41  
% 2.82/1.41  %Foreground sorts:
% 2.82/1.41  
% 2.82/1.41  
% 2.82/1.41  %Background operators:
% 2.82/1.41  
% 2.82/1.41  
% 2.82/1.41  %Foreground operators:
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.82/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.82/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.82/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.41  
% 2.82/1.42  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 2.82/1.42  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.82/1.42  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.82/1.42  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.82/1.42  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.82/1.42  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.82/1.42  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.82/1.42  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.82/1.42  tff(c_119, plain, (![A_34, B_35, C_36]: (k9_subset_1(A_34, B_35, C_36)=k3_xboole_0(B_35, C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.82/1.42  tff(c_127, plain, (![B_35]: (k9_subset_1('#skF_1', B_35, '#skF_3')=k3_xboole_0(B_35, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_119])).
% 2.82/1.42  tff(c_179, plain, (![A_39, B_40, C_41]: (m1_subset_1(k9_subset_1(A_39, B_40, C_41), k1_zfmisc_1(A_39)) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.82/1.42  tff(c_192, plain, (![B_35]: (m1_subset_1(k3_xboole_0(B_35, '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_127, c_179])).
% 2.82/1.42  tff(c_199, plain, (![B_35]: (m1_subset_1(k3_xboole_0(B_35, '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_192])).
% 2.82/1.42  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.42  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.82/1.42  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(k3_subset_1(A_7, B_8), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.42  tff(c_81, plain, (![A_30, B_31]: (k3_subset_1(A_30, k3_subset_1(A_30, B_31))=B_31 | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.82/1.42  tff(c_90, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_22, c_81])).
% 2.82/1.42  tff(c_222, plain, (![C_44, A_45, B_46]: (r1_tarski(C_44, k3_subset_1(A_45, B_46)) | ~r1_tarski(B_46, k3_subset_1(A_45, C_44)) | ~m1_subset_1(C_44, k1_zfmisc_1(A_45)) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.82/1.42  tff(c_224, plain, (![B_46]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', B_46)) | ~r1_tarski(B_46, '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_46, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_222])).
% 2.82/1.42  tff(c_284, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_224])).
% 2.82/1.42  tff(c_287, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_284])).
% 2.82/1.42  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_287])).
% 2.82/1.42  tff(c_795, plain, (![B_74]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', B_74)) | ~r1_tarski(B_74, '#skF_2') | ~m1_subset_1(B_74, k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_224])).
% 2.82/1.42  tff(c_18, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k9_subset_1('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.82/1.42  tff(c_129, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_18])).
% 2.82/1.42  tff(c_800, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_795, c_129])).
% 2.82/1.42  tff(c_823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_2, c_800])).
% 2.82/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.42  
% 2.82/1.42  Inference rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Ref     : 0
% 2.82/1.42  #Sup     : 212
% 2.82/1.42  #Fact    : 0
% 2.82/1.42  #Define  : 0
% 2.82/1.42  #Split   : 3
% 2.82/1.42  #Chain   : 0
% 2.82/1.42  #Close   : 0
% 2.82/1.42  
% 2.82/1.42  Ordering : KBO
% 2.82/1.42  
% 2.82/1.42  Simplification rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Subsume      : 1
% 2.82/1.42  #Demod        : 131
% 2.82/1.42  #Tautology    : 116
% 2.82/1.42  #SimpNegUnit  : 0
% 2.82/1.42  #BackRed      : 5
% 2.82/1.42  
% 2.82/1.42  #Partial instantiations: 0
% 2.82/1.42  #Strategies tried      : 1
% 2.82/1.42  
% 2.82/1.42  Timing (in seconds)
% 2.82/1.42  ----------------------
% 2.82/1.43  Preprocessing        : 0.28
% 2.82/1.43  Parsing              : 0.16
% 2.82/1.43  CNF conversion       : 0.02
% 2.82/1.43  Main loop            : 0.37
% 2.82/1.43  Inferencing          : 0.14
% 2.82/1.43  Reduction            : 0.13
% 2.82/1.43  Demodulation         : 0.10
% 2.82/1.43  BG Simplification    : 0.02
% 2.82/1.43  Subsumption          : 0.06
% 2.82/1.43  Abstraction          : 0.02
% 2.82/1.43  MUC search           : 0.00
% 2.82/1.43  Cooper               : 0.00
% 2.82/1.43  Total                : 0.68
% 2.82/1.43  Index Insertion      : 0.00
% 2.82/1.43  Index Deletion       : 0.00
% 2.82/1.43  Index Matching       : 0.00
% 2.82/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
