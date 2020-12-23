%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:23 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   47 (  59 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  73 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_41,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_45,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41,c_39])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_144,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_8,c_125])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_35])).

tff(c_46,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_27] : k4_xboole_0(A_27,A_27) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_46])).

tff(c_86,plain,(
    ! [A_28] : r1_tarski(k1_xboole_0,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [A_28] : k4_xboole_0(k1_xboole_0,A_28) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_4])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_351,plain,(
    ! [A_45,B_46,C_47] : k4_xboole_0(k4_xboole_0(A_45,B_46),C_47) = k4_xboole_0(A_45,k2_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_399,plain,(
    ! [C_47] : k4_xboole_0('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_47)) = k4_xboole_0(k1_xboole_0,C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_351])).

tff(c_569,plain,(
    ! [C_52] : k4_xboole_0('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_52)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_399])).

tff(c_605,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_569])).

tff(c_622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_605])).

tff(c_623,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_746,plain,(
    ! [A_64,C_65,B_66] :
      ( r1_xboole_0(A_64,C_65)
      | ~ r1_xboole_0(B_66,C_65)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1283,plain,(
    ! [A_87,B_88,A_89] :
      ( r1_xboole_0(A_87,B_88)
      | ~ r1_tarski(A_87,k4_xboole_0(A_89,B_88)) ) ),
    inference(resolution,[status(thm)],[c_16,c_746])).

tff(c_1332,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1283])).

tff(c_1346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_623,c_1332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:17:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.47  
% 2.88/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.48  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.88/1.48  
% 2.88/1.48  %Foreground sorts:
% 2.88/1.48  
% 2.88/1.48  
% 2.88/1.48  %Background operators:
% 2.88/1.48  
% 2.88/1.48  
% 2.88/1.48  %Foreground operators:
% 2.88/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.88/1.48  
% 2.88/1.49  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.88/1.49  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.88/1.49  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.88/1.49  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.88/1.49  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.88/1.49  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.88/1.49  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.88/1.49  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.88/1.49  tff(c_41, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | k4_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.49  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.88/1.49  tff(c_39, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 2.88/1.49  tff(c_45, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_41, c_39])).
% 2.88/1.49  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.49  tff(c_125, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.88/1.49  tff(c_144, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_8, c_125])).
% 2.88/1.49  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.49  tff(c_35, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.49  tff(c_38, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_35])).
% 2.88/1.49  tff(c_46, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.49  tff(c_63, plain, (![A_27]: (k4_xboole_0(A_27, A_27)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_46])).
% 2.88/1.49  tff(c_86, plain, (![A_28]: (r1_tarski(k1_xboole_0, A_28))), inference(superposition, [status(thm), theory('equality')], [c_63, c_8])).
% 2.88/1.49  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.49  tff(c_90, plain, (![A_28]: (k4_xboole_0(k1_xboole_0, A_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_86, c_4])).
% 2.88/1.49  tff(c_20, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.88/1.49  tff(c_62, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_46])).
% 2.88/1.49  tff(c_351, plain, (![A_45, B_46, C_47]: (k4_xboole_0(k4_xboole_0(A_45, B_46), C_47)=k4_xboole_0(A_45, k2_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.88/1.49  tff(c_399, plain, (![C_47]: (k4_xboole_0('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_47))=k4_xboole_0(k1_xboole_0, C_47))), inference(superposition, [status(thm), theory('equality')], [c_62, c_351])).
% 2.88/1.49  tff(c_569, plain, (![C_52]: (k4_xboole_0('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_52))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_399])).
% 2.88/1.49  tff(c_605, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_144, c_569])).
% 2.88/1.49  tff(c_622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_605])).
% 2.88/1.49  tff(c_623, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 2.88/1.49  tff(c_16, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.88/1.49  tff(c_746, plain, (![A_64, C_65, B_66]: (r1_xboole_0(A_64, C_65) | ~r1_xboole_0(B_66, C_65) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.88/1.49  tff(c_1283, plain, (![A_87, B_88, A_89]: (r1_xboole_0(A_87, B_88) | ~r1_tarski(A_87, k4_xboole_0(A_89, B_88)))), inference(resolution, [status(thm)], [c_16, c_746])).
% 2.88/1.49  tff(c_1332, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_1283])).
% 2.88/1.49  tff(c_1346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_623, c_1332])).
% 2.88/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.49  
% 2.88/1.49  Inference rules
% 2.88/1.49  ----------------------
% 2.88/1.49  #Ref     : 0
% 2.88/1.49  #Sup     : 329
% 2.88/1.49  #Fact    : 0
% 2.88/1.49  #Define  : 0
% 2.88/1.49  #Split   : 1
% 2.88/1.49  #Chain   : 0
% 2.88/1.49  #Close   : 0
% 2.88/1.49  
% 2.88/1.49  Ordering : KBO
% 2.88/1.49  
% 2.88/1.49  Simplification rules
% 2.88/1.49  ----------------------
% 2.88/1.49  #Subsume      : 9
% 2.88/1.49  #Demod        : 152
% 2.88/1.49  #Tautology    : 227
% 2.88/1.49  #SimpNegUnit  : 2
% 2.88/1.49  #BackRed      : 0
% 2.88/1.49  
% 2.88/1.49  #Partial instantiations: 0
% 2.88/1.49  #Strategies tried      : 1
% 2.88/1.49  
% 2.88/1.49  Timing (in seconds)
% 2.88/1.49  ----------------------
% 2.88/1.49  Preprocessing        : 0.26
% 2.88/1.49  Parsing              : 0.15
% 2.88/1.49  CNF conversion       : 0.02
% 2.88/1.49  Main loop            : 0.44
% 2.88/1.49  Inferencing          : 0.18
% 2.88/1.49  Reduction            : 0.14
% 2.88/1.49  Demodulation         : 0.11
% 2.88/1.49  BG Simplification    : 0.02
% 2.88/1.49  Subsumption          : 0.06
% 2.88/1.49  Abstraction          : 0.02
% 2.88/1.49  MUC search           : 0.00
% 2.88/1.49  Cooper               : 0.00
% 2.88/1.49  Total                : 0.73
% 2.88/1.49  Index Insertion      : 0.00
% 2.88/1.49  Index Deletion       : 0.00
% 2.88/1.49  Index Matching       : 0.00
% 2.88/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
