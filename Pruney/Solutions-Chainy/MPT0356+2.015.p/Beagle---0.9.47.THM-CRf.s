%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:57 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 (  85 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_67,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_47,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_16] : ~ v1_xboole_0(k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_66,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(B_38,A_39)
      | ~ m1_subset_1(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_11] : k3_tarski(k1_zfmisc_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,k3_tarski(B_27))
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [A_26,A_11] :
      ( r1_tarski(A_26,A_11)
      | ~ r2_hidden(A_26,k1_zfmisc_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_58])).

tff(c_73,plain,(
    ! [B_38,A_11] :
      ( r1_tarski(B_38,A_11)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_66,c_61])).

tff(c_112,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(B_42,A_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_73])).

tff(c_124,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_112])).

tff(c_28,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_78,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k3_subset_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_90,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_78])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    ! [A_45] :
      ( r1_xboole_0(A_45,'#skF_3')
      | ~ r1_tarski(A_45,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_4])).

tff(c_136,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_132])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_139,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_91,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_78])).

tff(c_144,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(A_46,k4_xboole_0(B_47,C_48))
      | ~ r1_xboole_0(A_46,C_48)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_51,'#skF_2')
      | ~ r1_tarski(A_51,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_144])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_170,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_161,c_26])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_139,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.03/1.23  
% 2.03/1.23  %Foreground sorts:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Background operators:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Foreground operators:
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.03/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.23  
% 2.03/1.24  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.03/1.24  tff(f_67, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.03/1.24  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.03/1.24  tff(f_47, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.03/1.24  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.03/1.24  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.03/1.24  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.03/1.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.03/1.24  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.03/1.24  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.03/1.24  tff(c_24, plain, (![A_16]: (~v1_xboole_0(k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.03/1.24  tff(c_66, plain, (![B_38, A_39]: (r2_hidden(B_38, A_39) | ~m1_subset_1(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.24  tff(c_12, plain, (![A_11]: (k3_tarski(k1_zfmisc_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.24  tff(c_58, plain, (![A_26, B_27]: (r1_tarski(A_26, k3_tarski(B_27)) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.24  tff(c_61, plain, (![A_26, A_11]: (r1_tarski(A_26, A_11) | ~r2_hidden(A_26, k1_zfmisc_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_58])).
% 2.03/1.24  tff(c_73, plain, (![B_38, A_11]: (r1_tarski(B_38, A_11) | ~m1_subset_1(B_38, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_66, c_61])).
% 2.03/1.24  tff(c_112, plain, (![B_42, A_43]: (r1_tarski(B_42, A_43) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)))), inference(negUnitSimplification, [status(thm)], [c_24, c_73])).
% 2.03/1.24  tff(c_124, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_112])).
% 2.03/1.24  tff(c_28, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.03/1.24  tff(c_78, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k3_subset_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.03/1.24  tff(c_90, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_78])).
% 2.03/1.24  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.24  tff(c_132, plain, (![A_45]: (r1_xboole_0(A_45, '#skF_3') | ~r1_tarski(A_45, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_4])).
% 2.03/1.24  tff(c_136, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_132])).
% 2.03/1.24  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.24  tff(c_139, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_136, c_2])).
% 2.03/1.24  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.03/1.24  tff(c_91, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_78])).
% 2.03/1.24  tff(c_144, plain, (![A_46, B_47, C_48]: (r1_tarski(A_46, k4_xboole_0(B_47, C_48)) | ~r1_xboole_0(A_46, C_48) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.03/1.24  tff(c_161, plain, (![A_51]: (r1_tarski(A_51, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_51, '#skF_2') | ~r1_tarski(A_51, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_144])).
% 2.03/1.24  tff(c_26, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.03/1.24  tff(c_170, plain, (~r1_xboole_0('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_161, c_26])).
% 2.03/1.24  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_139, c_170])).
% 2.03/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.24  
% 2.03/1.24  Inference rules
% 2.03/1.24  ----------------------
% 2.03/1.24  #Ref     : 0
% 2.03/1.24  #Sup     : 33
% 2.03/1.24  #Fact    : 0
% 2.03/1.24  #Define  : 0
% 2.03/1.24  #Split   : 0
% 2.03/1.24  #Chain   : 0
% 2.03/1.24  #Close   : 0
% 2.03/1.24  
% 2.03/1.24  Ordering : KBO
% 2.03/1.24  
% 2.03/1.24  Simplification rules
% 2.03/1.24  ----------------------
% 2.03/1.24  #Subsume      : 4
% 2.03/1.24  #Demod        : 4
% 2.03/1.24  #Tautology    : 14
% 2.03/1.24  #SimpNegUnit  : 1
% 2.03/1.24  #BackRed      : 0
% 2.03/1.24  
% 2.03/1.24  #Partial instantiations: 0
% 2.03/1.24  #Strategies tried      : 1
% 2.03/1.24  
% 2.03/1.24  Timing (in seconds)
% 2.03/1.24  ----------------------
% 2.03/1.24  Preprocessing        : 0.30
% 2.03/1.24  Parsing              : 0.16
% 2.03/1.24  CNF conversion       : 0.02
% 2.03/1.24  Main loop            : 0.16
% 2.03/1.24  Inferencing          : 0.07
% 2.03/1.24  Reduction            : 0.04
% 2.03/1.24  Demodulation         : 0.03
% 2.03/1.24  BG Simplification    : 0.01
% 2.03/1.24  Subsumption          : 0.03
% 2.03/1.24  Abstraction          : 0.01
% 2.03/1.24  MUC search           : 0.00
% 2.03/1.24  Cooper               : 0.00
% 2.03/1.24  Total                : 0.48
% 2.03/1.24  Index Insertion      : 0.00
% 2.03/1.24  Index Deletion       : 0.00
% 2.03/1.24  Index Matching       : 0.00
% 2.03/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
