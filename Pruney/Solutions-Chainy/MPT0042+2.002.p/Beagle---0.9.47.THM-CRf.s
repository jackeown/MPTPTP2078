%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:43 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k4_xboole_0(A,D),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [C_13,B_12,A_11] :
      ( r1_tarski(k4_xboole_0(C_13,B_12),k4_xboole_0(C_13,A_11))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_tarski(k4_xboole_0(A_26,C_27),k4_xboole_0(B_28,C_27))
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [A_33,C_34,B_35] :
      ( k3_xboole_0(k4_xboole_0(A_33,C_34),k4_xboole_0(B_35,C_34)) = k4_xboole_0(A_33,C_34)
      | ~ r1_tarski(A_33,B_35) ) ),
    inference(resolution,[status(thm)],[c_124,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(A_18,B_19)
      | ~ r1_tarski(A_18,k3_xboole_0(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_18,B_2,A_1] :
      ( r1_tarski(A_18,B_2)
      | ~ r1_tarski(A_18,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86])).

tff(c_346,plain,(
    ! [A_59,B_60,C_61,A_62] :
      ( r1_tarski(A_59,k4_xboole_0(B_60,C_61))
      | ~ r1_tarski(A_59,k4_xboole_0(A_62,C_61))
      | ~ r1_tarski(A_62,B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_101])).

tff(c_353,plain,(
    ! [C_63,B_64,B_65,A_66] :
      ( r1_tarski(k4_xboole_0(C_63,B_64),k4_xboole_0(B_65,A_66))
      | ~ r1_tarski(C_63,B_65)
      | ~ r1_tarski(A_66,B_64) ) ),
    inference(resolution,[status(thm)],[c_10,c_346])).

tff(c_12,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_4'),k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_364,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_353,c_12])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.24  
% 2.08/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.24  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.08/1.24  
% 2.08/1.24  %Foreground sorts:
% 2.08/1.24  
% 2.08/1.24  
% 2.08/1.24  %Background operators:
% 2.08/1.24  
% 2.08/1.24  
% 2.08/1.24  %Foreground operators:
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.24  
% 2.08/1.25  tff(f_50, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k4_xboole_0(A, D), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_xboole_1)).
% 2.08/1.25  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 2.08/1.25  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_xboole_1)).
% 2.08/1.25  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.08/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.08/1.25  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.08/1.25  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.25  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.25  tff(c_10, plain, (![C_13, B_12, A_11]: (r1_tarski(k4_xboole_0(C_13, B_12), k4_xboole_0(C_13, A_11)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.25  tff(c_124, plain, (![A_26, C_27, B_28]: (r1_tarski(k4_xboole_0(A_26, C_27), k4_xboole_0(B_28, C_27)) | ~r1_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.25  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.25  tff(c_135, plain, (![A_33, C_34, B_35]: (k3_xboole_0(k4_xboole_0(A_33, C_34), k4_xboole_0(B_35, C_34))=k4_xboole_0(A_33, C_34) | ~r1_tarski(A_33, B_35))), inference(resolution, [status(thm)], [c_124, c_6])).
% 2.08/1.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.25  tff(c_86, plain, (![A_18, B_19, C_20]: (r1_tarski(A_18, B_19) | ~r1_tarski(A_18, k3_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.25  tff(c_101, plain, (![A_18, B_2, A_1]: (r1_tarski(A_18, B_2) | ~r1_tarski(A_18, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_86])).
% 2.08/1.25  tff(c_346, plain, (![A_59, B_60, C_61, A_62]: (r1_tarski(A_59, k4_xboole_0(B_60, C_61)) | ~r1_tarski(A_59, k4_xboole_0(A_62, C_61)) | ~r1_tarski(A_62, B_60))), inference(superposition, [status(thm), theory('equality')], [c_135, c_101])).
% 2.08/1.25  tff(c_353, plain, (![C_63, B_64, B_65, A_66]: (r1_tarski(k4_xboole_0(C_63, B_64), k4_xboole_0(B_65, A_66)) | ~r1_tarski(C_63, B_65) | ~r1_tarski(A_66, B_64))), inference(resolution, [status(thm)], [c_10, c_346])).
% 2.08/1.25  tff(c_12, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_4'), k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.25  tff(c_364, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_353, c_12])).
% 2.08/1.25  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_364])).
% 2.08/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  Inference rules
% 2.08/1.25  ----------------------
% 2.08/1.25  #Ref     : 0
% 2.08/1.25  #Sup     : 99
% 2.08/1.25  #Fact    : 0
% 2.08/1.25  #Define  : 0
% 2.08/1.25  #Split   : 2
% 2.08/1.25  #Chain   : 0
% 2.08/1.25  #Close   : 0
% 2.08/1.25  
% 2.08/1.25  Ordering : KBO
% 2.08/1.25  
% 2.08/1.25  Simplification rules
% 2.08/1.25  ----------------------
% 2.08/1.25  #Subsume      : 26
% 2.08/1.25  #Demod        : 5
% 2.08/1.25  #Tautology    : 40
% 2.08/1.25  #SimpNegUnit  : 0
% 2.08/1.25  #BackRed      : 0
% 2.08/1.25  
% 2.08/1.25  #Partial instantiations: 0
% 2.08/1.25  #Strategies tried      : 1
% 2.08/1.25  
% 2.08/1.25  Timing (in seconds)
% 2.08/1.25  ----------------------
% 2.08/1.26  Preprocessing        : 0.25
% 2.08/1.26  Parsing              : 0.14
% 2.08/1.26  CNF conversion       : 0.01
% 2.08/1.26  Main loop            : 0.26
% 2.08/1.26  Inferencing          : 0.10
% 2.08/1.26  Reduction            : 0.07
% 2.08/1.26  Demodulation         : 0.05
% 2.08/1.26  BG Simplification    : 0.02
% 2.08/1.26  Subsumption          : 0.06
% 2.08/1.26  Abstraction          : 0.01
% 2.08/1.26  MUC search           : 0.00
% 2.08/1.26  Cooper               : 0.00
% 2.08/1.26  Total                : 0.53
% 2.08/1.26  Index Insertion      : 0.00
% 2.08/1.26  Index Deletion       : 0.00
% 2.08/1.26  Index Matching       : 0.00
% 2.08/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
