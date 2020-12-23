%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:58 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  57 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17,plain,(
    ! [A_11,B_12] :
      ( k3_subset_1(A_11,k3_subset_1(A_11,B_12)) = B_12
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_17])).

tff(c_62,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k3_subset_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k3_subset_1(A_4,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_158,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,k3_subset_1(A_26,B_27)) = k3_subset_1(A_26,k3_subset_1(A_26,B_27))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(resolution,[status(thm)],[c_62,c_4])).

tff(c_162,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_158])).

tff(c_167,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_162])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k3_subset_1(A_13,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_24])).

tff(c_49,plain,(
    ! [C_15,B_16,A_17] :
      ( r1_tarski(k4_xboole_0(C_15,B_16),k4_xboole_0(C_15,A_17))
      | ~ r1_tarski(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [B_16] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_16),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_49])).

tff(c_196,plain,
    ( r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_55])).

tff(c_215,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_196])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.57  
% 2.34/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.58  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.34/1.58  
% 2.34/1.58  %Foreground sorts:
% 2.34/1.58  
% 2.34/1.58  
% 2.34/1.58  %Background operators:
% 2.34/1.58  
% 2.34/1.58  
% 2.34/1.58  %Foreground operators:
% 2.34/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.34/1.58  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.58  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.58  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.58  
% 2.34/1.59  tff(f_51, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.34/1.59  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.34/1.59  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.34/1.59  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.34/1.59  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 2.34/1.59  tff(c_10, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.59  tff(c_12, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.59  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.59  tff(c_17, plain, (![A_11, B_12]: (k3_subset_1(A_11, k3_subset_1(A_11, B_12))=B_12 | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.59  tff(c_22, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_14, c_17])).
% 2.34/1.59  tff(c_62, plain, (![A_18, B_19]: (m1_subset_1(k3_subset_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.59  tff(c_4, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k3_subset_1(A_4, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.59  tff(c_158, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_subset_1(A_26, B_27))=k3_subset_1(A_26, k3_subset_1(A_26, B_27)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(resolution, [status(thm)], [c_62, c_4])).
% 2.34/1.59  tff(c_162, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_158])).
% 2.34/1.59  tff(c_167, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_162])).
% 2.34/1.59  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.59  tff(c_24, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k3_subset_1(A_13, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.59  tff(c_32, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_24])).
% 2.34/1.59  tff(c_49, plain, (![C_15, B_16, A_17]: (r1_tarski(k4_xboole_0(C_15, B_16), k4_xboole_0(C_15, A_17)) | ~r1_tarski(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.59  tff(c_55, plain, (![B_16]: (r1_tarski(k4_xboole_0('#skF_1', B_16), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', B_16))), inference(superposition, [status(thm), theory('equality')], [c_32, c_49])).
% 2.34/1.59  tff(c_196, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_55])).
% 2.34/1.59  tff(c_215, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_196])).
% 2.34/1.59  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_215])).
% 2.34/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.59  
% 2.34/1.59  Inference rules
% 2.34/1.59  ----------------------
% 2.34/1.59  #Ref     : 0
% 2.34/1.59  #Sup     : 58
% 2.34/1.59  #Fact    : 0
% 2.34/1.59  #Define  : 0
% 2.34/1.59  #Split   : 4
% 2.34/1.59  #Chain   : 0
% 2.34/1.59  #Close   : 0
% 2.34/1.59  
% 2.34/1.59  Ordering : KBO
% 2.34/1.59  
% 2.34/1.59  Simplification rules
% 2.34/1.59  ----------------------
% 2.34/1.59  #Subsume      : 3
% 2.34/1.59  #Demod        : 12
% 2.34/1.59  #Tautology    : 25
% 2.34/1.59  #SimpNegUnit  : 1
% 2.34/1.59  #BackRed      : 0
% 2.34/1.59  
% 2.34/1.59  #Partial instantiations: 0
% 2.34/1.59  #Strategies tried      : 1
% 2.34/1.59  
% 2.34/1.59  Timing (in seconds)
% 2.34/1.59  ----------------------
% 2.34/1.60  Preprocessing        : 0.44
% 2.34/1.60  Parsing              : 0.23
% 2.34/1.60  CNF conversion       : 0.03
% 2.34/1.60  Main loop            : 0.28
% 2.34/1.60  Inferencing          : 0.11
% 2.34/1.60  Reduction            : 0.08
% 2.34/1.60  Demodulation         : 0.06
% 2.34/1.60  BG Simplification    : 0.02
% 2.34/1.60  Subsumption          : 0.06
% 2.34/1.60  Abstraction          : 0.02
% 2.34/1.60  MUC search           : 0.00
% 2.34/1.60  Cooper               : 0.00
% 2.34/1.60  Total                : 0.77
% 2.34/1.60  Index Insertion      : 0.00
% 2.34/1.60  Index Deletion       : 0.00
% 2.34/1.60  Index Matching       : 0.00
% 2.34/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
