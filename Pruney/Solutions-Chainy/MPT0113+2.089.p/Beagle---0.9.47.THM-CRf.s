%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:23 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   50 (  63 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  71 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_45,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | k4_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_43,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_49,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_43])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_37,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_80,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_80])).

tff(c_268,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_312,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_268])).

tff(c_321,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_312])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_80])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_625,plain,(
    ! [A_64,B_65,C_66] : k4_xboole_0(k3_xboole_0(A_64,B_65),C_66) = k3_xboole_0(A_64,k4_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1222,plain,(
    ! [C_87] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_87)) = k4_xboole_0('#skF_1',C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_625])).

tff(c_1266,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1222])).

tff(c_1283,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_1266])).

tff(c_1285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_1283])).

tff(c_1286,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1290,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(A_91,B_92) = A_91
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1308,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_1290])).

tff(c_1787,plain,(
    ! [A_119,B_120,C_121] : k4_xboole_0(k3_xboole_0(A_119,B_120),C_121) = k3_xboole_0(A_119,k4_xboole_0(B_120,C_121)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2194,plain,(
    ! [A_131,B_132,C_133] : r1_xboole_0(k3_xboole_0(A_131,k4_xboole_0(B_132,C_133)),C_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_1787,c_20])).

tff(c_2239,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_2194])).

tff(c_2258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1286,c_2239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.57  
% 3.08/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.57  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.08/1.57  
% 3.08/1.57  %Foreground sorts:
% 3.08/1.57  
% 3.08/1.57  
% 3.08/1.57  %Background operators:
% 3.08/1.57  
% 3.08/1.57  
% 3.08/1.57  %Foreground operators:
% 3.08/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.08/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.08/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.08/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.08/1.57  
% 3.08/1.58  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.08/1.58  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.08/1.58  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.08/1.58  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.08/1.58  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.08/1.58  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.08/1.58  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.08/1.58  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.08/1.58  tff(c_45, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | k4_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.58  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.08/1.58  tff(c_43, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 3.08/1.58  tff(c_49, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_45, c_43])).
% 3.08/1.58  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.08/1.58  tff(c_34, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.58  tff(c_37, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_34])).
% 3.08/1.58  tff(c_80, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.58  tff(c_95, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_37, c_80])).
% 3.08/1.58  tff(c_268, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.08/1.58  tff(c_312, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_268])).
% 3.08/1.58  tff(c_321, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_95, c_312])).
% 3.08/1.58  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.58  tff(c_96, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_80])).
% 3.08/1.58  tff(c_24, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.08/1.58  tff(c_50, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.08/1.58  tff(c_64, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_50])).
% 3.08/1.58  tff(c_625, plain, (![A_64, B_65, C_66]: (k4_xboole_0(k3_xboole_0(A_64, B_65), C_66)=k3_xboole_0(A_64, k4_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.08/1.58  tff(c_1222, plain, (![C_87]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_87))=k4_xboole_0('#skF_1', C_87))), inference(superposition, [status(thm), theory('equality')], [c_64, c_625])).
% 3.08/1.58  tff(c_1266, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96, c_1222])).
% 3.08/1.58  tff(c_1283, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_321, c_1266])).
% 3.08/1.58  tff(c_1285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_1283])).
% 3.08/1.58  tff(c_1286, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 3.08/1.58  tff(c_1290, plain, (![A_91, B_92]: (k3_xboole_0(A_91, B_92)=A_91 | ~r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.08/1.58  tff(c_1308, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_1290])).
% 3.08/1.58  tff(c_1787, plain, (![A_119, B_120, C_121]: (k4_xboole_0(k3_xboole_0(A_119, B_120), C_121)=k3_xboole_0(A_119, k4_xboole_0(B_120, C_121)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.08/1.58  tff(c_20, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.58  tff(c_2194, plain, (![A_131, B_132, C_133]: (r1_xboole_0(k3_xboole_0(A_131, k4_xboole_0(B_132, C_133)), C_133))), inference(superposition, [status(thm), theory('equality')], [c_1787, c_20])).
% 3.08/1.58  tff(c_2239, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1308, c_2194])).
% 3.08/1.58  tff(c_2258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1286, c_2239])).
% 3.08/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.58  
% 3.08/1.58  Inference rules
% 3.08/1.58  ----------------------
% 3.08/1.58  #Ref     : 0
% 3.08/1.58  #Sup     : 561
% 3.08/1.58  #Fact    : 0
% 3.08/1.58  #Define  : 0
% 3.08/1.58  #Split   : 1
% 3.08/1.58  #Chain   : 0
% 3.08/1.58  #Close   : 0
% 3.08/1.58  
% 3.08/1.58  Ordering : KBO
% 3.08/1.58  
% 3.08/1.58  Simplification rules
% 3.08/1.58  ----------------------
% 3.08/1.58  #Subsume      : 5
% 3.08/1.58  #Demod        : 349
% 3.08/1.58  #Tautology    : 389
% 3.08/1.58  #SimpNegUnit  : 2
% 3.08/1.58  #BackRed      : 0
% 3.08/1.58  
% 3.08/1.58  #Partial instantiations: 0
% 3.08/1.58  #Strategies tried      : 1
% 3.08/1.59  
% 3.08/1.59  Timing (in seconds)
% 3.08/1.59  ----------------------
% 3.08/1.59  Preprocessing        : 0.27
% 3.08/1.59  Parsing              : 0.15
% 3.08/1.59  CNF conversion       : 0.02
% 3.08/1.59  Main loop            : 0.50
% 3.08/1.59  Inferencing          : 0.19
% 3.08/1.59  Reduction            : 0.18
% 3.08/1.59  Demodulation         : 0.14
% 3.08/1.59  BG Simplification    : 0.02
% 3.08/1.59  Subsumption          : 0.07
% 3.08/1.59  Abstraction          : 0.03
% 3.08/1.59  MUC search           : 0.00
% 3.08/1.59  Cooper               : 0.00
% 3.08/1.59  Total                : 0.80
% 3.08/1.59  Index Insertion      : 0.00
% 3.08/1.59  Index Deletion       : 0.00
% 3.08/1.59  Index Matching       : 0.00
% 3.08/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
