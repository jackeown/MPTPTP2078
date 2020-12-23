%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:47 EST 2020

% Result     : Theorem 8.83s
% Output     : CNFRefutation 8.97s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 120 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 ( 132 expanded)
%              Number of equality atoms :   50 ( 108 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_28,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_61,plain,(
    ! [B_27,A_28] :
      ( r1_xboole_0(B_27,A_28)
      | ~ r1_xboole_0(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_171,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_171])).

tff(c_216,plain,(
    ! [A_38,B_39] : k2_xboole_0(k3_xboole_0(A_38,B_39),k4_xboole_0(A_38,B_39)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_228,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_4')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_216])).

tff(c_80,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_30] : k2_xboole_0(k1_xboole_0,A_30) = A_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_10])).

tff(c_525,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_96])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_385,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_424,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_385])).

tff(c_430,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_424])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_35,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_14,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_566,plain,(
    ! [A_49,B_50] : k2_xboole_0(A_49,k4_xboole_0(B_50,A_49)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_600,plain,(
    ! [B_13,A_12] : k2_xboole_0(B_13,k4_xboole_0(A_12,B_13)) = k2_xboole_0(B_13,k2_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_566])).

tff(c_680,plain,(
    ! [B_52,A_53] : k2_xboole_0(B_52,k2_xboole_0(A_53,B_52)) = k2_xboole_0(B_52,A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_600])).

tff(c_724,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_680])).

tff(c_738,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_2,c_724])).

tff(c_1108,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_18])).

tff(c_1114,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_1108])).

tff(c_1255,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k4_xboole_0(A_65,B_66),C_67) = k4_xboole_0(A_65,k2_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_17614,plain,(
    ! [C_192,A_193,B_194] : k2_xboole_0(C_192,k4_xboole_0(A_193,k2_xboole_0(B_194,C_192))) = k2_xboole_0(C_192,k4_xboole_0(A_193,B_194)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1255,c_14])).

tff(c_17966,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_17614])).

tff(c_18121,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_10,c_17966])).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_191,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_171])).

tff(c_231,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_1')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_216])).

tff(c_248,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_96])).

tff(c_1278,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k2_xboole_0(B_66,k4_xboole_0(A_65,B_66))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1255,c_430])).

tff(c_1360,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k2_xboole_0(B_66,A_65)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1278])).

tff(c_18425,plain,(
    ! [A_195] : k2_xboole_0('#skF_2',k4_xboole_0(A_195,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_2',k4_xboole_0(A_195,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_17614])).

tff(c_18607,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_18425])).

tff(c_18679,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18121,c_2,c_248,c_10,c_18607])).

tff(c_18681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_18679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:47:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.83/3.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.72  
% 8.97/3.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.72  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.97/3.72  
% 8.97/3.72  %Foreground sorts:
% 8.97/3.72  
% 8.97/3.72  
% 8.97/3.72  %Background operators:
% 8.97/3.72  
% 8.97/3.72  
% 8.97/3.72  %Foreground operators:
% 8.97/3.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.97/3.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.97/3.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.97/3.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.97/3.72  tff('#skF_2', type, '#skF_2': $i).
% 8.97/3.72  tff('#skF_3', type, '#skF_3': $i).
% 8.97/3.72  tff('#skF_1', type, '#skF_1': $i).
% 8.97/3.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.97/3.72  tff('#skF_4', type, '#skF_4': $i).
% 8.97/3.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.97/3.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.97/3.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.97/3.72  
% 8.97/3.73  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 8.97/3.73  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.97/3.73  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.97/3.73  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 8.97/3.73  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.97/3.73  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.97/3.73  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.97/3.73  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.97/3.73  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.97/3.73  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.97/3.73  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.97/3.73  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.97/3.73  tff(c_28, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.97/3.73  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.97/3.73  tff(c_61, plain, (![B_27, A_28]: (r1_xboole_0(B_27, A_28) | ~r1_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.97/3.73  tff(c_66, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_61])).
% 8.97/3.73  tff(c_171, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.97/3.73  tff(c_189, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_171])).
% 8.97/3.73  tff(c_216, plain, (![A_38, B_39]: (k2_xboole_0(k3_xboole_0(A_38, B_39), k4_xboole_0(A_38, B_39))=A_38)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.97/3.73  tff(c_228, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_4'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_189, c_216])).
% 8.97/3.73  tff(c_80, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.97/3.73  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.97/3.73  tff(c_96, plain, (![A_30]: (k2_xboole_0(k1_xboole_0, A_30)=A_30)), inference(superposition, [status(thm), theory('equality')], [c_80, c_10])).
% 8.97/3.73  tff(c_525, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_228, c_96])).
% 8.97/3.73  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.97/3.73  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.97/3.73  tff(c_385, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.97/3.73  tff(c_424, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_385])).
% 8.97/3.73  tff(c_430, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_424])).
% 8.97/3.73  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.97/3.73  tff(c_34, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.97/3.73  tff(c_35, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 8.97/3.73  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.97/3.73  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.97/3.73  tff(c_566, plain, (![A_49, B_50]: (k2_xboole_0(A_49, k4_xboole_0(B_50, A_49))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.97/3.73  tff(c_600, plain, (![B_13, A_12]: (k2_xboole_0(B_13, k4_xboole_0(A_12, B_13))=k2_xboole_0(B_13, k2_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_566])).
% 8.97/3.73  tff(c_680, plain, (![B_52, A_53]: (k2_xboole_0(B_52, k2_xboole_0(A_53, B_52))=k2_xboole_0(B_52, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_600])).
% 8.97/3.73  tff(c_724, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35, c_680])).
% 8.97/3.73  tff(c_738, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_2, c_724])).
% 8.97/3.73  tff(c_1108, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_738, c_18])).
% 8.97/3.73  tff(c_1114, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_430, c_1108])).
% 8.97/3.73  tff(c_1255, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k4_xboole_0(A_65, B_66), C_67)=k4_xboole_0(A_65, k2_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.97/3.73  tff(c_17614, plain, (![C_192, A_193, B_194]: (k2_xboole_0(C_192, k4_xboole_0(A_193, k2_xboole_0(B_194, C_192)))=k2_xboole_0(C_192, k4_xboole_0(A_193, B_194)))), inference(superposition, [status(thm), theory('equality')], [c_1255, c_14])).
% 8.97/3.73  tff(c_17966, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1114, c_17614])).
% 8.97/3.73  tff(c_18121, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_525, c_10, c_17966])).
% 8.97/3.73  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.97/3.73  tff(c_191, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_171])).
% 8.97/3.73  tff(c_231, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_1'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_191, c_216])).
% 8.97/3.73  tff(c_248, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_231, c_96])).
% 8.97/3.73  tff(c_1278, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k2_xboole_0(B_66, k4_xboole_0(A_65, B_66)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1255, c_430])).
% 8.97/3.73  tff(c_1360, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k2_xboole_0(B_66, A_65))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1278])).
% 8.97/3.73  tff(c_18425, plain, (![A_195]: (k2_xboole_0('#skF_2', k4_xboole_0(A_195, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_2', k4_xboole_0(A_195, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_35, c_17614])).
% 8.97/3.73  tff(c_18607, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1360, c_18425])).
% 8.97/3.73  tff(c_18679, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18121, c_2, c_248, c_10, c_18607])).
% 8.97/3.73  tff(c_18681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_18679])).
% 8.97/3.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.73  
% 8.97/3.73  Inference rules
% 8.97/3.73  ----------------------
% 8.97/3.73  #Ref     : 0
% 8.97/3.73  #Sup     : 4734
% 8.97/3.73  #Fact    : 0
% 8.97/3.73  #Define  : 0
% 8.97/3.73  #Split   : 0
% 8.97/3.73  #Chain   : 0
% 8.97/3.73  #Close   : 0
% 8.97/3.73  
% 8.97/3.73  Ordering : KBO
% 8.97/3.73  
% 8.97/3.73  Simplification rules
% 8.97/3.73  ----------------------
% 8.97/3.73  #Subsume      : 82
% 8.97/3.73  #Demod        : 6190
% 8.97/3.73  #Tautology    : 2783
% 8.97/3.73  #SimpNegUnit  : 1
% 8.97/3.73  #BackRed      : 7
% 8.97/3.73  
% 8.97/3.73  #Partial instantiations: 0
% 8.97/3.73  #Strategies tried      : 1
% 8.97/3.73  
% 8.97/3.73  Timing (in seconds)
% 8.97/3.73  ----------------------
% 8.97/3.73  Preprocessing        : 0.29
% 8.97/3.73  Parsing              : 0.16
% 8.97/3.73  CNF conversion       : 0.02
% 8.97/3.73  Main loop            : 2.68
% 8.97/3.73  Inferencing          : 0.49
% 8.97/3.73  Reduction            : 1.67
% 8.97/3.73  Demodulation         : 1.52
% 8.97/3.73  BG Simplification    : 0.06
% 8.97/3.73  Subsumption          : 0.35
% 8.97/3.73  Abstraction          : 0.10
% 8.97/3.73  MUC search           : 0.00
% 8.97/3.73  Cooper               : 0.00
% 8.97/3.73  Total                : 3.00
% 8.97/3.73  Index Insertion      : 0.00
% 8.97/3.74  Index Deletion       : 0.00
% 8.97/3.74  Index Matching       : 0.00
% 8.97/3.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
