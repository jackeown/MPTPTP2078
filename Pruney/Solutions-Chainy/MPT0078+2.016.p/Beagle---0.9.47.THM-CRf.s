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
% DateTime   : Thu Dec  3 09:43:40 EST 2020

% Result     : Theorem 5.30s
% Output     : CNFRefutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 140 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 ( 148 expanded)
%              Number of equality atoms :   47 ( 131 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_20,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [A_24,B_25] : k4_xboole_0(k2_xboole_0(A_24,B_25),B_25) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = k2_xboole_0(A_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_12])).

tff(c_127,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_109])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_121,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_102])).

tff(c_129,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_121])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_115,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_102])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_387,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_421,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_387])).

tff(c_426,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_421])).

tff(c_628,plain,(
    ! [A_42,B_43,C_44] : k4_xboole_0(k4_xboole_0(A_42,B_43),C_44) = k4_xboole_0(A_42,k2_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4742,plain,(
    ! [C_105,A_106,B_107] : k2_xboole_0(C_105,k4_xboole_0(A_106,k2_xboole_0(B_107,C_105))) = k2_xboole_0(C_105,k4_xboole_0(A_106,B_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_10])).

tff(c_4941,plain,(
    ! [C_105,B_107] : k2_xboole_0(C_105,k4_xboole_0(k2_xboole_0(B_107,C_105),B_107)) = k2_xboole_0(C_105,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_4742])).

tff(c_5031,plain,(
    ! [C_108,B_109] : k2_xboole_0(C_108,k4_xboole_0(C_108,B_109)) = C_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_127,c_4941])).

tff(c_5225,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_5031])).

tff(c_131,plain,(
    ! [A_26] : k2_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_109])).

tff(c_154,plain,(
    ! [B_2] : k2_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_87,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_415,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_387])).

tff(c_425,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_415])).

tff(c_528,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_10])).

tff(c_532,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_2,c_2,c_528])).

tff(c_6129,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5225,c_532])).

tff(c_5024,plain,(
    ! [C_105,B_107] : k2_xboole_0(C_105,k4_xboole_0(C_105,B_107)) = C_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_127,c_4941])).

tff(c_400,plain,(
    ! [A_34,B_35] : k2_xboole_0(k4_xboole_0(A_34,B_35),k3_xboole_0(A_34,B_35)) = k2_xboole_0(k4_xboole_0(A_34,B_35),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_10])).

tff(c_423,plain,(
    ! [A_34,B_35] : k2_xboole_0(k4_xboole_0(A_34,B_35),k3_xboole_0(A_34,B_35)) = k2_xboole_0(A_34,k4_xboole_0(A_34,B_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_400])).

tff(c_6380,plain,(
    ! [A_116,B_117] : k2_xboole_0(k4_xboole_0(A_116,B_117),k3_xboole_0(A_116,B_117)) = A_116 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5024,c_423])).

tff(c_6473,plain,(
    k2_xboole_0('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6129,c_6380])).

tff(c_6621,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_88,c_6473])).

tff(c_6623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_6621])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.30/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.07  
% 5.30/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.07  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.30/2.07  
% 5.30/2.07  %Foreground sorts:
% 5.30/2.07  
% 5.30/2.07  
% 5.30/2.07  %Background operators:
% 5.30/2.07  
% 5.30/2.07  
% 5.30/2.07  %Foreground operators:
% 5.30/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.30/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.30/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.30/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.30/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.30/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.30/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.30/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.30/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.30/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.30/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.30/2.07  
% 5.30/2.08  tff(f_52, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 5.30/2.08  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.30/2.08  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.30/2.08  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.30/2.08  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.30/2.08  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.30/2.08  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.30/2.08  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.30/2.08  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.30/2.08  tff(c_20, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.30/2.08  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.30/2.08  tff(c_102, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, B_25), B_25)=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.30/2.08  tff(c_109, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=k2_xboole_0(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_102, c_12])).
% 5.30/2.08  tff(c_127, plain, (![A_24]: (k2_xboole_0(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_109])).
% 5.30/2.08  tff(c_24, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.30/2.08  tff(c_80, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.30/2.08  tff(c_88, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_80])).
% 5.30/2.08  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.30/2.08  tff(c_26, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.30/2.08  tff(c_121, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_102])).
% 5.30/2.08  tff(c_129, plain, (k4_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_121])).
% 5.30/2.08  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.30/2.08  tff(c_115, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_102])).
% 5.30/2.08  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.30/2.08  tff(c_387, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.30/2.08  tff(c_421, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_387])).
% 5.30/2.08  tff(c_426, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_421])).
% 5.30/2.08  tff(c_628, plain, (![A_42, B_43, C_44]: (k4_xboole_0(k4_xboole_0(A_42, B_43), C_44)=k4_xboole_0(A_42, k2_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.30/2.08  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.30/2.08  tff(c_4742, plain, (![C_105, A_106, B_107]: (k2_xboole_0(C_105, k4_xboole_0(A_106, k2_xboole_0(B_107, C_105)))=k2_xboole_0(C_105, k4_xboole_0(A_106, B_107)))), inference(superposition, [status(thm), theory('equality')], [c_628, c_10])).
% 5.30/2.08  tff(c_4941, plain, (![C_105, B_107]: (k2_xboole_0(C_105, k4_xboole_0(k2_xboole_0(B_107, C_105), B_107))=k2_xboole_0(C_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_426, c_4742])).
% 5.30/2.08  tff(c_5031, plain, (![C_108, B_109]: (k2_xboole_0(C_108, k4_xboole_0(C_108, B_109))=C_108)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_127, c_4941])).
% 5.30/2.08  tff(c_5225, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_129, c_5031])).
% 5.30/2.08  tff(c_131, plain, (![A_26]: (k2_xboole_0(A_26, k1_xboole_0)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_109])).
% 5.30/2.08  tff(c_154, plain, (![B_2]: (k2_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_131])).
% 5.30/2.08  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.30/2.08  tff(c_87, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_80])).
% 5.30/2.08  tff(c_415, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_129, c_387])).
% 5.30/2.08  tff(c_425, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_87, c_415])).
% 5.30/2.08  tff(c_528, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_425, c_10])).
% 5.30/2.08  tff(c_532, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_2, c_2, c_528])).
% 5.30/2.08  tff(c_6129, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5225, c_532])).
% 5.30/2.08  tff(c_5024, plain, (![C_105, B_107]: (k2_xboole_0(C_105, k4_xboole_0(C_105, B_107))=C_105)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_127, c_4941])).
% 5.30/2.08  tff(c_400, plain, (![A_34, B_35]: (k2_xboole_0(k4_xboole_0(A_34, B_35), k3_xboole_0(A_34, B_35))=k2_xboole_0(k4_xboole_0(A_34, B_35), A_34))), inference(superposition, [status(thm), theory('equality')], [c_387, c_10])).
% 5.30/2.08  tff(c_423, plain, (![A_34, B_35]: (k2_xboole_0(k4_xboole_0(A_34, B_35), k3_xboole_0(A_34, B_35))=k2_xboole_0(A_34, k4_xboole_0(A_34, B_35)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_400])).
% 5.30/2.08  tff(c_6380, plain, (![A_116, B_117]: (k2_xboole_0(k4_xboole_0(A_116, B_117), k3_xboole_0(A_116, B_117))=A_116)), inference(demodulation, [status(thm), theory('equality')], [c_5024, c_423])).
% 5.30/2.08  tff(c_6473, plain, (k2_xboole_0('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6129, c_6380])).
% 5.30/2.08  tff(c_6621, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_88, c_6473])).
% 5.30/2.08  tff(c_6623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_6621])).
% 5.30/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.08  
% 5.30/2.08  Inference rules
% 5.30/2.08  ----------------------
% 5.30/2.08  #Ref     : 0
% 5.30/2.08  #Sup     : 1665
% 5.30/2.08  #Fact    : 0
% 5.30/2.08  #Define  : 0
% 5.30/2.08  #Split   : 0
% 5.30/2.08  #Chain   : 0
% 5.30/2.08  #Close   : 0
% 5.30/2.08  
% 5.30/2.08  Ordering : KBO
% 5.30/2.08  
% 5.30/2.08  Simplification rules
% 5.30/2.08  ----------------------
% 5.30/2.08  #Subsume      : 15
% 5.30/2.08  #Demod        : 2030
% 5.30/2.08  #Tautology    : 1213
% 5.30/2.08  #SimpNegUnit  : 1
% 5.30/2.08  #BackRed      : 13
% 5.30/2.08  
% 5.30/2.08  #Partial instantiations: 0
% 5.30/2.08  #Strategies tried      : 1
% 5.30/2.08  
% 5.30/2.08  Timing (in seconds)
% 5.30/2.08  ----------------------
% 5.30/2.09  Preprocessing        : 0.30
% 5.30/2.09  Parsing              : 0.16
% 5.30/2.09  CNF conversion       : 0.02
% 5.30/2.09  Main loop            : 1.02
% 5.30/2.09  Inferencing          : 0.30
% 5.30/2.09  Reduction            : 0.51
% 5.30/2.09  Demodulation         : 0.44
% 5.30/2.09  BG Simplification    : 0.03
% 5.30/2.09  Subsumption          : 0.13
% 5.30/2.09  Abstraction          : 0.05
% 5.30/2.09  MUC search           : 0.00
% 5.30/2.09  Cooper               : 0.00
% 5.30/2.09  Total                : 1.34
% 5.30/2.09  Index Insertion      : 0.00
% 5.30/2.09  Index Deletion       : 0.00
% 5.30/2.09  Index Matching       : 0.00
% 5.30/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
