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
% DateTime   : Thu Dec  3 09:42:50 EST 2020

% Result     : Theorem 36.69s
% Output     : CNFRefutation 36.69s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  49 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k4_xboole_0(A,B),C)
       => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_38,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_51,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_24])).

tff(c_20,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [C_12,B_11,A_10] :
      ( r1_tarski(k4_xboole_0(C_12,B_11),k4_xboole_0(C_12,A_10))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(B_49,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2954,plain,(
    ! [A_159,C_160,B_161,A_162] :
      ( r1_tarski(A_159,k2_xboole_0(C_160,B_161))
      | ~ r1_tarski(A_159,A_162)
      | ~ r1_tarski(A_162,B_161) ) ),
    inference(resolution,[status(thm)],[c_2,c_115])).

tff(c_71649,plain,(
    ! [B_815,A_817,C_818,B_816,C_819] :
      ( r1_tarski(k4_xboole_0(C_819,B_816),k2_xboole_0(C_818,B_815))
      | ~ r1_tarski(k4_xboole_0(C_819,A_817),B_815)
      | ~ r1_tarski(A_817,B_816) ) ),
    inference(resolution,[status(thm)],[c_8,c_2954])).

tff(c_72613,plain,(
    ! [B_822,C_823] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_822),k2_xboole_0(C_823,'#skF_3'))
      | ~ r1_tarski('#skF_2',B_822) ) ),
    inference(resolution,[status(thm)],[c_26,c_71649])).

tff(c_231,plain,(
    ! [C_65,B_66,A_67] :
      ( r1_tarski(k4_xboole_0(C_65,B_66),k4_xboole_0(C_65,A_67))
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k4_xboole_0(B_16,A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_271,plain,(
    ! [C_65,B_66] :
      ( k4_xboole_0(C_65,B_66) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_65,B_66),B_66) ) ),
    inference(resolution,[status(thm)],[c_231,c_14])).

tff(c_149582,plain,(
    ! [C_1204] :
      ( k4_xboole_0('#skF_1',k2_xboole_0(C_1204,'#skF_3')) = k1_xboole_0
      | ~ r1_tarski('#skF_2',k2_xboole_0(C_1204,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_72613,c_271])).

tff(c_149664,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_149582])).

tff(c_149688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_149664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.69/28.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.69/28.97  
% 36.69/28.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.69/28.97  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 36.69/28.97  
% 36.69/28.97  %Foreground sorts:
% 36.69/28.97  
% 36.69/28.97  
% 36.69/28.97  %Background operators:
% 36.69/28.97  
% 36.69/28.97  
% 36.69/28.97  %Foreground operators:
% 36.69/28.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.69/28.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 36.69/28.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.69/28.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.69/28.97  tff('#skF_2', type, '#skF_2': $i).
% 36.69/28.97  tff('#skF_3', type, '#skF_3': $i).
% 36.69/28.97  tff('#skF_1', type, '#skF_1': $i).
% 36.69/28.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.69/28.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.69/28.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.69/28.97  
% 36.69/28.98  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 36.69/28.98  tff(f_72, negated_conjecture, ~(![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 36.69/28.98  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 36.69/28.98  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 36.69/28.98  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 36.69/28.98  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 36.69/28.98  tff(f_51, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 36.69/28.98  tff(c_38, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 36.69/28.98  tff(c_24, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 36.69/28.98  tff(c_51, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_24])).
% 36.69/28.98  tff(c_20, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 36.69/28.98  tff(c_26, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 36.69/28.98  tff(c_8, plain, (![C_12, B_11, A_10]: (r1_tarski(k4_xboole_0(C_12, B_11), k4_xboole_0(C_12, A_10)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.69/28.98  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 36.69/28.98  tff(c_115, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(B_49, C_48) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_39])).
% 36.69/28.98  tff(c_2954, plain, (![A_159, C_160, B_161, A_162]: (r1_tarski(A_159, k2_xboole_0(C_160, B_161)) | ~r1_tarski(A_159, A_162) | ~r1_tarski(A_162, B_161))), inference(resolution, [status(thm)], [c_2, c_115])).
% 36.69/28.98  tff(c_71649, plain, (![B_815, A_817, C_818, B_816, C_819]: (r1_tarski(k4_xboole_0(C_819, B_816), k2_xboole_0(C_818, B_815)) | ~r1_tarski(k4_xboole_0(C_819, A_817), B_815) | ~r1_tarski(A_817, B_816))), inference(resolution, [status(thm)], [c_8, c_2954])).
% 36.69/28.98  tff(c_72613, plain, (![B_822, C_823]: (r1_tarski(k4_xboole_0('#skF_1', B_822), k2_xboole_0(C_823, '#skF_3')) | ~r1_tarski('#skF_2', B_822))), inference(resolution, [status(thm)], [c_26, c_71649])).
% 36.69/28.98  tff(c_231, plain, (![C_65, B_66, A_67]: (r1_tarski(k4_xboole_0(C_65, B_66), k4_xboole_0(C_65, A_67)) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.69/28.98  tff(c_14, plain, (![A_15, B_16]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k4_xboole_0(B_16, A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 36.69/28.98  tff(c_271, plain, (![C_65, B_66]: (k4_xboole_0(C_65, B_66)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_65, B_66), B_66))), inference(resolution, [status(thm)], [c_231, c_14])).
% 36.69/28.98  tff(c_149582, plain, (![C_1204]: (k4_xboole_0('#skF_1', k2_xboole_0(C_1204, '#skF_3'))=k1_xboole_0 | ~r1_tarski('#skF_2', k2_xboole_0(C_1204, '#skF_3')))), inference(resolution, [status(thm)], [c_72613, c_271])).
% 36.69/28.98  tff(c_149664, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_149582])).
% 36.69/28.98  tff(c_149688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_149664])).
% 36.69/28.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.69/28.98  
% 36.69/28.98  Inference rules
% 36.69/28.98  ----------------------
% 36.69/28.98  #Ref     : 0
% 36.69/28.98  #Sup     : 36332
% 36.69/28.98  #Fact    : 0
% 36.69/28.98  #Define  : 0
% 36.69/28.98  #Split   : 1
% 36.69/28.98  #Chain   : 0
% 36.69/28.98  #Close   : 0
% 36.69/28.98  
% 36.69/28.98  Ordering : KBO
% 36.69/28.98  
% 36.69/28.98  Simplification rules
% 36.69/28.98  ----------------------
% 36.69/28.98  #Subsume      : 6470
% 36.69/28.98  #Demod        : 29958
% 36.69/28.98  #Tautology    : 17605
% 36.69/28.98  #SimpNegUnit  : 97
% 36.69/28.98  #BackRed      : 0
% 36.69/28.98  
% 36.69/28.98  #Partial instantiations: 0
% 36.69/28.98  #Strategies tried      : 1
% 36.69/28.98  
% 36.69/28.98  Timing (in seconds)
% 36.69/28.98  ----------------------
% 36.69/28.98  Preprocessing        : 0.27
% 36.69/28.98  Parsing              : 0.15
% 36.69/28.98  CNF conversion       : 0.02
% 36.69/28.98  Main loop            : 27.89
% 36.69/28.98  Inferencing          : 1.98
% 36.69/28.98  Reduction            : 13.40
% 36.69/28.98  Demodulation         : 11.83
% 36.69/28.98  BG Simplification    : 0.25
% 36.69/28.98  Subsumption          : 11.31
% 36.69/28.98  Abstraction          : 0.33
% 36.69/28.98  MUC search           : 0.00
% 36.69/28.98  Cooper               : 0.00
% 36.69/28.98  Total                : 28.19
% 36.69/28.98  Index Insertion      : 0.00
% 36.69/28.98  Index Deletion       : 0.00
% 36.69/28.98  Index Matching       : 0.00
% 36.69/28.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
