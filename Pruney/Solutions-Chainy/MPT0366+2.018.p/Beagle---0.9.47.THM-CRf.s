%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:46 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   44 (  64 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 134 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( ( r1_tarski(B,C)
                    & r1_xboole_0(D,C) )
                 => r1_tarski(B,k3_subset_1(A,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_28])).

tff(c_41,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_xboole_0(A_22,k4_xboole_0(C_23,B_24))
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    ! [A_22] :
      ( r1_xboole_0(A_22,'#skF_4')
      | ~ r1_tarski(A_22,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_41])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_34,B_35] :
      ( k3_subset_1(A_34,k3_subset_1(A_34,B_35)) = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_97])).

tff(c_152,plain,(
    ! [B_46,A_47,C_48] :
      ( r1_xboole_0(B_46,k3_subset_1(A_47,C_48))
      | ~ r1_tarski(B_46,C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_164,plain,(
    ! [B_46] :
      ( r1_xboole_0(B_46,'#skF_4')
      | ~ r1_tarski(B_46,k3_subset_1('#skF_1','#skF_4'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_4'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_46,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_152])).

tff(c_547,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_550,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_547])).

tff(c_554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_550])).

tff(c_556,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_255,plain,(
    ! [B_63,C_64,A_65] :
      ( r1_tarski(B_63,C_64)
      | ~ r1_xboole_0(B_63,k3_subset_1(A_65,C_64))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_278,plain,(
    ! [B_63] :
      ( r1_tarski(B_63,k3_subset_1('#skF_1','#skF_4'))
      | ~ r1_xboole_0(B_63,'#skF_4')
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_4'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_63,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_255])).

tff(c_835,plain,(
    ! [B_104] :
      ( r1_tarski(B_104,k3_subset_1('#skF_1','#skF_4'))
      | ~ r1_xboole_0(B_104,'#skF_4')
      | ~ m1_subset_1(B_104,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_278])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_848,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_835,c_16])).

tff(c_857,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_848])).

tff(c_872,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_857])).

tff(c_883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_872])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.49  
% 3.15/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.49  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.15/1.49  
% 3.15/1.49  %Foreground sorts:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Background operators:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Foreground operators:
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.15/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.15/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.49  
% 3.15/1.50  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 3.15/1.50  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.15/1.50  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.15/1.50  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.15/1.50  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.15/1.50  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 3.15/1.50  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.50  tff(c_18, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.50  tff(c_28, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.50  tff(c_36, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_18, c_28])).
% 3.15/1.50  tff(c_41, plain, (![A_22, C_23, B_24]: (r1_xboole_0(A_22, k4_xboole_0(C_23, B_24)) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.50  tff(c_47, plain, (![A_22]: (r1_xboole_0(A_22, '#skF_4') | ~r1_tarski(A_22, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_41])).
% 3.15/1.50  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.50  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.50  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.50  tff(c_97, plain, (![A_34, B_35]: (k3_subset_1(A_34, k3_subset_1(A_34, B_35))=B_35 | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.50  tff(c_107, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_22, c_97])).
% 3.15/1.50  tff(c_152, plain, (![B_46, A_47, C_48]: (r1_xboole_0(B_46, k3_subset_1(A_47, C_48)) | ~r1_tarski(B_46, C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(A_47)) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.15/1.50  tff(c_164, plain, (![B_46]: (r1_xboole_0(B_46, '#skF_4') | ~r1_tarski(B_46, k3_subset_1('#skF_1', '#skF_4')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_46, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_107, c_152])).
% 3.15/1.50  tff(c_547, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_4'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_164])).
% 3.15/1.50  tff(c_550, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_547])).
% 3.15/1.50  tff(c_554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_550])).
% 3.15/1.50  tff(c_556, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_4'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_164])).
% 3.15/1.50  tff(c_255, plain, (![B_63, C_64, A_65]: (r1_tarski(B_63, C_64) | ~r1_xboole_0(B_63, k3_subset_1(A_65, C_64)) | ~m1_subset_1(C_64, k1_zfmisc_1(A_65)) | ~m1_subset_1(B_63, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.15/1.50  tff(c_278, plain, (![B_63]: (r1_tarski(B_63, k3_subset_1('#skF_1', '#skF_4')) | ~r1_xboole_0(B_63, '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_63, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_107, c_255])).
% 3.15/1.50  tff(c_835, plain, (![B_104]: (r1_tarski(B_104, k3_subset_1('#skF_1', '#skF_4')) | ~r1_xboole_0(B_104, '#skF_4') | ~m1_subset_1(B_104, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_278])).
% 3.15/1.50  tff(c_16, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.50  tff(c_848, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_835, c_16])).
% 3.15/1.50  tff(c_857, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_848])).
% 3.15/1.50  tff(c_872, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_47, c_857])).
% 3.15/1.50  tff(c_883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_872])).
% 3.15/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.50  
% 3.15/1.50  Inference rules
% 3.15/1.50  ----------------------
% 3.15/1.50  #Ref     : 0
% 3.15/1.50  #Sup     : 205
% 3.15/1.50  #Fact    : 0
% 3.15/1.50  #Define  : 0
% 3.15/1.50  #Split   : 19
% 3.15/1.50  #Chain   : 0
% 3.15/1.50  #Close   : 0
% 3.15/1.50  
% 3.15/1.50  Ordering : KBO
% 3.15/1.50  
% 3.15/1.50  Simplification rules
% 3.15/1.50  ----------------------
% 3.15/1.50  #Subsume      : 35
% 3.15/1.50  #Demod        : 36
% 3.15/1.50  #Tautology    : 39
% 3.15/1.50  #SimpNegUnit  : 10
% 3.15/1.50  #BackRed      : 0
% 3.15/1.50  
% 3.15/1.50  #Partial instantiations: 0
% 3.15/1.50  #Strategies tried      : 1
% 3.15/1.50  
% 3.15/1.50  Timing (in seconds)
% 3.15/1.50  ----------------------
% 3.15/1.50  Preprocessing        : 0.26
% 3.15/1.50  Parsing              : 0.14
% 3.15/1.50  CNF conversion       : 0.02
% 3.15/1.50  Main loop            : 0.42
% 3.15/1.50  Inferencing          : 0.16
% 3.15/1.50  Reduction            : 0.12
% 3.15/1.50  Demodulation         : 0.08
% 3.15/1.50  BG Simplification    : 0.02
% 3.15/1.50  Subsumption          : 0.10
% 3.15/1.50  Abstraction          : 0.02
% 3.15/1.50  MUC search           : 0.00
% 3.15/1.50  Cooper               : 0.00
% 3.15/1.50  Total                : 0.71
% 3.15/1.50  Index Insertion      : 0.00
% 3.15/1.50  Index Deletion       : 0.00
% 3.15/1.50  Index Matching       : 0.00
% 3.15/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
