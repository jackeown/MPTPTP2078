%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:35 EST 2020

% Result     : Theorem 5.08s
% Output     : CNFRefutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  63 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_20,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_143,plain,(
    ! [A_30,B_31,C_32] :
      ( k9_subset_1(A_30,B_31,C_32) = k3_xboole_0(B_31,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [B_31] : k9_subset_1('#skF_1',B_31,'#skF_3') = k3_xboole_0(B_31,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_143])).

tff(c_255,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k9_subset_1(A_39,B_40,C_41),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_266,plain,(
    ! [B_31] :
      ( m1_subset_1(k3_xboole_0(B_31,'#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_255])).

tff(c_281,plain,(
    ! [B_43] : m1_subset_1(k3_xboole_0(B_43,'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_266])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k3_subset_1(A_8,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_399,plain,(
    ! [B_49] : k4_xboole_0('#skF_1',k3_xboole_0(B_49,'#skF_3')) = k3_subset_1('#skF_1',k3_xboole_0(B_49,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_281,c_8])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k3_subset_1(A_26,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_46])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( r1_tarski(k4_xboole_0(C_3,B_2),k4_xboole_0(C_3,A_1))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [A_1] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k4_xboole_0('#skF_1',A_1))
      | ~ r1_tarski(A_1,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_2741,plain,(
    ! [B_159] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0(B_159,'#skF_3')))
      | ~ r1_tarski(k3_xboole_0(B_159,'#skF_3'),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_74])).

tff(c_14,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k9_subset_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_150,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_14])).

tff(c_2744,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2741,c_150])).

tff(c_2748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_2744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:02:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.08/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.94  
% 5.08/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.94  %$ r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.08/1.94  
% 5.08/1.94  %Foreground sorts:
% 5.08/1.94  
% 5.08/1.94  
% 5.08/1.94  %Background operators:
% 5.08/1.94  
% 5.08/1.94  
% 5.08/1.94  %Foreground operators:
% 5.08/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.08/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.08/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.08/1.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.08/1.94  tff('#skF_2', type, '#skF_2': $i).
% 5.08/1.94  tff('#skF_3', type, '#skF_3': $i).
% 5.08/1.94  tff('#skF_1', type, '#skF_1': $i).
% 5.08/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.08/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.08/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.08/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.08/1.94  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.08/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.08/1.94  
% 5.08/1.95  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.08/1.95  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.08/1.95  tff(f_53, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 5.08/1.95  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.08/1.95  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 5.08/1.95  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.08/1.95  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 5.08/1.95  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.08/1.95  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.08/1.95  tff(c_29, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4])).
% 5.08/1.95  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/1.95  tff(c_143, plain, (![A_30, B_31, C_32]: (k9_subset_1(A_30, B_31, C_32)=k3_xboole_0(B_31, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.08/1.95  tff(c_148, plain, (![B_31]: (k9_subset_1('#skF_1', B_31, '#skF_3')=k3_xboole_0(B_31, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_143])).
% 5.08/1.95  tff(c_255, plain, (![A_39, B_40, C_41]: (m1_subset_1(k9_subset_1(A_39, B_40, C_41), k1_zfmisc_1(A_39)) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.08/1.95  tff(c_266, plain, (![B_31]: (m1_subset_1(k3_xboole_0(B_31, '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_148, c_255])).
% 5.08/1.95  tff(c_281, plain, (![B_43]: (m1_subset_1(k3_xboole_0(B_43, '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_266])).
% 5.08/1.95  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k3_subset_1(A_8, B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.08/1.95  tff(c_399, plain, (![B_49]: (k4_xboole_0('#skF_1', k3_xboole_0(B_49, '#skF_3'))=k3_subset_1('#skF_1', k3_xboole_0(B_49, '#skF_3')))), inference(resolution, [status(thm)], [c_281, c_8])).
% 5.08/1.95  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/1.95  tff(c_46, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k3_subset_1(A_26, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.08/1.95  tff(c_54, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_46])).
% 5.08/1.95  tff(c_2, plain, (![C_3, B_2, A_1]: (r1_tarski(k4_xboole_0(C_3, B_2), k4_xboole_0(C_3, A_1)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.08/1.95  tff(c_74, plain, (![A_1]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', A_1)) | ~r1_tarski(A_1, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 5.08/1.95  tff(c_2741, plain, (![B_159]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0(B_159, '#skF_3'))) | ~r1_tarski(k3_xboole_0(B_159, '#skF_3'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_74])).
% 5.08/1.95  tff(c_14, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k9_subset_1('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/1.95  tff(c_150, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_14])).
% 5.08/1.95  tff(c_2744, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2741, c_150])).
% 5.08/1.95  tff(c_2748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29, c_2744])).
% 5.08/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.95  
% 5.08/1.95  Inference rules
% 5.08/1.95  ----------------------
% 5.08/1.95  #Ref     : 0
% 5.08/1.95  #Sup     : 776
% 5.08/1.95  #Fact    : 0
% 5.08/1.95  #Define  : 0
% 5.08/1.95  #Split   : 22
% 5.08/1.95  #Chain   : 0
% 5.08/1.95  #Close   : 0
% 5.08/1.95  
% 5.08/1.95  Ordering : KBO
% 5.08/1.95  
% 5.08/1.95  Simplification rules
% 5.08/1.95  ----------------------
% 5.08/1.95  #Subsume      : 33
% 5.08/1.95  #Demod        : 219
% 5.08/1.95  #Tautology    : 98
% 5.08/1.95  #SimpNegUnit  : 0
% 5.08/1.95  #BackRed      : 3
% 5.08/1.95  
% 5.08/1.95  #Partial instantiations: 0
% 5.08/1.95  #Strategies tried      : 1
% 5.08/1.95  
% 5.08/1.95  Timing (in seconds)
% 5.08/1.95  ----------------------
% 5.08/1.96  Preprocessing        : 0.26
% 5.08/1.96  Parsing              : 0.14
% 5.08/1.96  CNF conversion       : 0.02
% 5.08/1.96  Main loop            : 0.93
% 5.08/1.96  Inferencing          : 0.29
% 5.08/1.96  Reduction            : 0.33
% 5.08/1.96  Demodulation         : 0.24
% 5.08/1.96  BG Simplification    : 0.04
% 5.08/1.96  Subsumption          : 0.21
% 5.08/1.96  Abstraction          : 0.04
% 5.08/1.96  MUC search           : 0.00
% 5.08/1.96  Cooper               : 0.00
% 5.08/1.96  Total                : 1.22
% 5.08/1.96  Index Insertion      : 0.00
% 5.08/1.96  Index Deletion       : 0.00
% 5.08/1.96  Index Matching       : 0.00
% 5.08/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
