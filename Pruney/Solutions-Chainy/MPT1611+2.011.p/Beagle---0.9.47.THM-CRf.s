%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:33 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   42 (  46 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  47 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_57,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_33,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_12,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_11] : k9_setfam_1(A_11) = k1_zfmisc_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_13] : k2_yellow_1(k9_setfam_1(A_13)) = k3_yellow_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_23,plain,(
    ! [A_13] : k2_yellow_1(k1_zfmisc_1(A_13)) = k3_yellow_1(A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_6,plain,(
    ! [A_5] : k3_tarski(k1_zfmisc_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [A_25] :
      ( k4_yellow_0(k2_yellow_1(A_25)) = k3_tarski(A_25)
      | ~ r2_hidden(k3_tarski(A_25),A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,(
    ! [A_5] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_5))) = k3_tarski(k1_zfmisc_1(A_5))
      | ~ r2_hidden(A_5,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_83,plain,(
    ! [A_5] :
      ( k4_yellow_0(k3_yellow_1(A_5)) = A_5
      | ~ r2_hidden(A_5,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_6,c_81])).

tff(c_85,plain,(
    ! [A_26] :
      ( k4_yellow_0(k3_yellow_1(A_26)) = A_26
      | ~ r2_hidden(A_26,k1_zfmisc_1(A_26)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_83])).

tff(c_89,plain,(
    ! [A_9] :
      ( k4_yellow_0(k3_yellow_1(A_9)) = A_9
      | v1_xboole_0(k1_zfmisc_1(A_9))
      | ~ m1_subset_1(A_9,k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_92,plain,(
    ! [A_9] :
      ( k4_yellow_0(k3_yellow_1(A_9)) = A_9
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_89])).

tff(c_93,plain,(
    ! [A_9] : k4_yellow_0(k3_yellow_1(A_9)) = A_9 ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_92])).

tff(c_22,plain,(
    k4_yellow_0(k3_yellow_1('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.46  
% 2.13/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.47  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2
% 2.13/1.47  
% 2.13/1.47  %Foreground sorts:
% 2.13/1.47  
% 2.13/1.47  
% 2.13/1.47  %Background operators:
% 2.13/1.47  
% 2.13/1.47  
% 2.13/1.47  %Foreground operators:
% 2.13/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.47  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.13/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.47  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.13/1.47  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.13/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.13/1.47  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.13/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.13/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.47  
% 2.13/1.48  tff(f_40, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.13/1.48  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.13/1.48  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.13/1.48  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.13/1.48  tff(f_48, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.13/1.48  tff(f_57, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.13/1.48  tff(f_33, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.13/1.48  tff(f_55, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.13/1.48  tff(f_60, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 2.13/1.48  tff(c_12, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.13/1.48  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.48  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.48  tff(c_24, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.13/1.48  tff(c_14, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.48  tff(c_16, plain, (![A_11]: (k9_setfam_1(A_11)=k1_zfmisc_1(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.48  tff(c_20, plain, (![A_13]: (k2_yellow_1(k9_setfam_1(A_13))=k3_yellow_1(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.48  tff(c_23, plain, (![A_13]: (k2_yellow_1(k1_zfmisc_1(A_13))=k3_yellow_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 2.13/1.48  tff(c_6, plain, (![A_5]: (k3_tarski(k1_zfmisc_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.48  tff(c_74, plain, (![A_25]: (k4_yellow_0(k2_yellow_1(A_25))=k3_tarski(A_25) | ~r2_hidden(k3_tarski(A_25), A_25) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.13/1.48  tff(c_81, plain, (![A_5]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_5)))=k3_tarski(k1_zfmisc_1(A_5)) | ~r2_hidden(A_5, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_74])).
% 2.13/1.48  tff(c_83, plain, (![A_5]: (k4_yellow_0(k3_yellow_1(A_5))=A_5 | ~r2_hidden(A_5, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_23, c_6, c_81])).
% 2.13/1.48  tff(c_85, plain, (![A_26]: (k4_yellow_0(k3_yellow_1(A_26))=A_26 | ~r2_hidden(A_26, k1_zfmisc_1(A_26)))), inference(negUnitSimplification, [status(thm)], [c_12, c_83])).
% 2.13/1.48  tff(c_89, plain, (![A_9]: (k4_yellow_0(k3_yellow_1(A_9))=A_9 | v1_xboole_0(k1_zfmisc_1(A_9)) | ~m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_14, c_85])).
% 2.13/1.48  tff(c_92, plain, (![A_9]: (k4_yellow_0(k3_yellow_1(A_9))=A_9 | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_89])).
% 2.13/1.48  tff(c_93, plain, (![A_9]: (k4_yellow_0(k3_yellow_1(A_9))=A_9)), inference(negUnitSimplification, [status(thm)], [c_12, c_92])).
% 2.13/1.48  tff(c_22, plain, (k4_yellow_0(k3_yellow_1('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.48  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_22])).
% 2.13/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.48  
% 2.13/1.48  Inference rules
% 2.13/1.48  ----------------------
% 2.13/1.48  #Ref     : 0
% 2.13/1.48  #Sup     : 13
% 2.13/1.48  #Fact    : 0
% 2.13/1.48  #Define  : 0
% 2.13/1.48  #Split   : 0
% 2.13/1.48  #Chain   : 0
% 2.13/1.48  #Close   : 0
% 2.13/1.48  
% 2.13/1.48  Ordering : KBO
% 2.13/1.48  
% 2.13/1.48  Simplification rules
% 2.13/1.48  ----------------------
% 2.13/1.48  #Subsume      : 0
% 2.13/1.48  #Demod        : 7
% 2.13/1.48  #Tautology    : 11
% 2.13/1.48  #SimpNegUnit  : 2
% 2.13/1.48  #BackRed      : 1
% 2.13/1.48  
% 2.13/1.48  #Partial instantiations: 0
% 2.13/1.48  #Strategies tried      : 1
% 2.13/1.48  
% 2.13/1.48  Timing (in seconds)
% 2.13/1.49  ----------------------
% 2.13/1.49  Preprocessing        : 0.47
% 2.13/1.49  Parsing              : 0.25
% 2.13/1.49  CNF conversion       : 0.03
% 2.13/1.49  Main loop            : 0.17
% 2.13/1.49  Inferencing          : 0.07
% 2.13/1.49  Reduction            : 0.05
% 2.13/1.49  Demodulation         : 0.04
% 2.13/1.49  BG Simplification    : 0.01
% 2.13/1.49  Subsumption          : 0.02
% 2.13/1.49  Abstraction          : 0.01
% 2.13/1.49  MUC search           : 0.00
% 2.13/1.49  Cooper               : 0.00
% 2.13/1.49  Total                : 0.69
% 2.13/1.49  Index Insertion      : 0.00
% 2.13/1.49  Index Deletion       : 0.00
% 2.13/1.49  Index Matching       : 0.00
% 2.13/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
