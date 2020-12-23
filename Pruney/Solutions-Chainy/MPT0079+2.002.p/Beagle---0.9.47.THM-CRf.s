%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:42 EST 2020

% Result     : Theorem 4.99s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 164 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :   78 ( 184 expanded)
%              Number of equality atoms :   62 ( 135 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_32,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_299,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(A_45,B_46) = B_46
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_400,plain,(
    ! [A_51,B_52] : k2_xboole_0(k4_xboole_0(A_51,B_52),A_51) = A_51 ),
    inference(resolution,[status(thm)],[c_20,c_299])).

tff(c_426,plain,(
    ! [B_2,B_52] : k2_xboole_0(B_2,k4_xboole_0(B_2,B_52)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_400])).

tff(c_24,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_204,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_211,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_204])).

tff(c_30,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_809,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3047,plain,(
    ! [A_110,B_111] : k4_xboole_0(A_110,k3_xboole_0(A_110,B_111)) = k3_xboole_0(A_110,k4_xboole_0(A_110,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_809])).

tff(c_3126,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_2')) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_3047])).

tff(c_3160,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3126])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_911,plain,(
    ! [A_68,B_69] : r1_tarski(k3_xboole_0(A_68,B_69),A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_20])).

tff(c_951,plain,(
    ! [B_70,A_71] : r1_tarski(k3_xboole_0(B_70,A_71),A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_911])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_982,plain,(
    ! [B_70,A_71] : k2_xboole_0(k3_xboole_0(B_70,A_71),A_71) = A_71 ),
    inference(resolution,[status(thm)],[c_951,c_14])).

tff(c_3374,plain,(
    k2_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_2')) = k4_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3160,c_982])).

tff(c_3397,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_3374])).

tff(c_286,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_298,plain,(
    ! [A_13,B_14] : k4_xboole_0(k4_xboole_0(A_13,B_14),A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_286])).

tff(c_992,plain,(
    ! [A_72,B_73,C_74] : k4_xboole_0(k4_xboole_0(A_72,B_73),C_74) = k4_xboole_0(A_72,k2_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1303,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k2_xboole_0(B_80,A_79)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_992])).

tff(c_1315,plain,(
    ! [A_79,B_80] : k3_xboole_0(A_79,k2_xboole_0(B_80,A_79)) = k4_xboole_0(A_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1303,c_30])).

tff(c_1381,plain,(
    ! [A_79,B_80] : k3_xboole_0(A_79,k2_xboole_0(B_80,A_79)) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1315])).

tff(c_26,plain,(
    ! [A_18,B_19] : k4_xboole_0(k2_xboole_0(A_18,B_19),B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_855,plain,(
    ! [A_18,B_19] : k4_xboole_0(k2_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_19)) = k3_xboole_0(k2_xboole_0(A_18,B_19),B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_809])).

tff(c_877,plain,(
    ! [A_18,B_19] : k4_xboole_0(k2_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_19)) = k3_xboole_0(B_19,k2_xboole_0(A_18,B_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_855])).

tff(c_3548,plain,(
    ! [A_113,B_114] : k4_xboole_0(k2_xboole_0(A_113,B_114),k4_xboole_0(A_113,B_114)) = B_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_877])).

tff(c_3599,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_2'),'#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3397,c_3548])).

tff(c_445,plain,(
    ! [A_53,B_54] : k4_xboole_0(k2_xboole_0(A_53,B_54),B_54) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_476,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_445])).

tff(c_3794,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3599,c_476])).

tff(c_16,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_1375,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_1303])).

tff(c_22,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5208,plain,(
    ! [C_127,A_128,B_129] : k2_xboole_0(C_127,k4_xboole_0(A_128,k2_xboole_0(B_129,C_127))) = k2_xboole_0(C_127,k4_xboole_0(A_128,B_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_22])).

tff(c_5311,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_5208])).

tff(c_5413,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3794,c_16,c_5311])).

tff(c_36,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_212,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_204])).

tff(c_3123,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_3047])).

tff(c_3159,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3123])).

tff(c_3172,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3159,c_982])).

tff(c_3195,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_3172])).

tff(c_1060,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(B_14,A_13)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_992])).

tff(c_5561,plain,(
    ! [A_130] : k2_xboole_0('#skF_2',k4_xboole_0(A_130,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_2',k4_xboole_0(A_130,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_5208])).

tff(c_5654,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_5561])).

tff(c_5706,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5413,c_2,c_3195,c_16,c_5654])).

tff(c_5708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_5706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.99/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/2.05  
% 4.99/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/2.05  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.99/2.05  
% 4.99/2.05  %Foreground sorts:
% 4.99/2.05  
% 4.99/2.05  
% 4.99/2.05  %Background operators:
% 4.99/2.05  
% 4.99/2.05  
% 4.99/2.05  %Foreground operators:
% 4.99/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.99/2.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.99/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.99/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.99/2.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.99/2.05  tff('#skF_2', type, '#skF_2': $i).
% 4.99/2.05  tff('#skF_3', type, '#skF_3': $i).
% 4.99/2.05  tff('#skF_1', type, '#skF_1': $i).
% 4.99/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.99/2.05  tff('#skF_4', type, '#skF_4': $i).
% 4.99/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.99/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.99/2.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.99/2.05  
% 4.99/2.07  tff(f_66, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 4.99/2.07  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.99/2.07  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.99/2.07  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.99/2.07  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.99/2.07  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.99/2.07  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.99/2.07  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.99/2.07  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.99/2.07  tff(f_55, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.99/2.07  tff(f_53, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.99/2.07  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.99/2.07  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.99/2.07  tff(c_32, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.99/2.07  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.99/2.07  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.99/2.07  tff(c_299, plain, (![A_45, B_46]: (k2_xboole_0(A_45, B_46)=B_46 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.99/2.07  tff(c_400, plain, (![A_51, B_52]: (k2_xboole_0(k4_xboole_0(A_51, B_52), A_51)=A_51)), inference(resolution, [status(thm)], [c_20, c_299])).
% 4.99/2.07  tff(c_426, plain, (![B_2, B_52]: (k2_xboole_0(B_2, k4_xboole_0(B_2, B_52))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_400])).
% 4.99/2.07  tff(c_24, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.99/2.07  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.99/2.07  tff(c_204, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.99/2.07  tff(c_211, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_204])).
% 4.99/2.07  tff(c_30, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.99/2.07  tff(c_809, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.99/2.07  tff(c_3047, plain, (![A_110, B_111]: (k4_xboole_0(A_110, k3_xboole_0(A_110, B_111))=k3_xboole_0(A_110, k4_xboole_0(A_110, B_111)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_809])).
% 4.99/2.07  tff(c_3126, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_2'))=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_211, c_3047])).
% 4.99/2.07  tff(c_3160, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3126])).
% 4.99/2.07  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.99/2.07  tff(c_911, plain, (![A_68, B_69]: (r1_tarski(k3_xboole_0(A_68, B_69), A_68))), inference(superposition, [status(thm), theory('equality')], [c_809, c_20])).
% 4.99/2.07  tff(c_951, plain, (![B_70, A_71]: (r1_tarski(k3_xboole_0(B_70, A_71), A_71))), inference(superposition, [status(thm), theory('equality')], [c_4, c_911])).
% 4.99/2.07  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.99/2.07  tff(c_982, plain, (![B_70, A_71]: (k2_xboole_0(k3_xboole_0(B_70, A_71), A_71)=A_71)), inference(resolution, [status(thm)], [c_951, c_14])).
% 4.99/2.07  tff(c_3374, plain, (k2_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_2'))=k4_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3160, c_982])).
% 4.99/2.07  tff(c_3397, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_426, c_3374])).
% 4.99/2.07  tff(c_286, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.99/2.07  tff(c_298, plain, (![A_13, B_14]: (k4_xboole_0(k4_xboole_0(A_13, B_14), A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_286])).
% 4.99/2.07  tff(c_992, plain, (![A_72, B_73, C_74]: (k4_xboole_0(k4_xboole_0(A_72, B_73), C_74)=k4_xboole_0(A_72, k2_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.99/2.07  tff(c_1303, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k2_xboole_0(B_80, A_79))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_298, c_992])).
% 4.99/2.07  tff(c_1315, plain, (![A_79, B_80]: (k3_xboole_0(A_79, k2_xboole_0(B_80, A_79))=k4_xboole_0(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1303, c_30])).
% 4.99/2.07  tff(c_1381, plain, (![A_79, B_80]: (k3_xboole_0(A_79, k2_xboole_0(B_80, A_79))=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1315])).
% 4.99/2.07  tff(c_26, plain, (![A_18, B_19]: (k4_xboole_0(k2_xboole_0(A_18, B_19), B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.99/2.07  tff(c_855, plain, (![A_18, B_19]: (k4_xboole_0(k2_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_19))=k3_xboole_0(k2_xboole_0(A_18, B_19), B_19))), inference(superposition, [status(thm), theory('equality')], [c_26, c_809])).
% 4.99/2.07  tff(c_877, plain, (![A_18, B_19]: (k4_xboole_0(k2_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_19))=k3_xboole_0(B_19, k2_xboole_0(A_18, B_19)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_855])).
% 4.99/2.07  tff(c_3548, plain, (![A_113, B_114]: (k4_xboole_0(k2_xboole_0(A_113, B_114), k4_xboole_0(A_113, B_114))=B_114)), inference(demodulation, [status(thm), theory('equality')], [c_1381, c_877])).
% 4.99/2.07  tff(c_3599, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_2'), '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3397, c_3548])).
% 4.99/2.07  tff(c_445, plain, (![A_53, B_54]: (k4_xboole_0(k2_xboole_0(A_53, B_54), B_54)=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.99/2.07  tff(c_476, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_445])).
% 4.99/2.07  tff(c_3794, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3599, c_476])).
% 4.99/2.07  tff(c_16, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.99/2.07  tff(c_38, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.99/2.07  tff(c_39, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 4.99/2.07  tff(c_1375, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_39, c_1303])).
% 4.99/2.07  tff(c_22, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.99/2.07  tff(c_5208, plain, (![C_127, A_128, B_129]: (k2_xboole_0(C_127, k4_xboole_0(A_128, k2_xboole_0(B_129, C_127)))=k2_xboole_0(C_127, k4_xboole_0(A_128, B_129)))), inference(superposition, [status(thm), theory('equality')], [c_992, c_22])).
% 4.99/2.07  tff(c_5311, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1375, c_5208])).
% 4.99/2.07  tff(c_5413, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3794, c_16, c_5311])).
% 4.99/2.07  tff(c_36, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.99/2.07  tff(c_212, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_204])).
% 4.99/2.07  tff(c_3123, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_212, c_3047])).
% 4.99/2.07  tff(c_3159, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3123])).
% 4.99/2.07  tff(c_3172, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3159, c_982])).
% 4.99/2.07  tff(c_3195, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_426, c_3172])).
% 4.99/2.07  tff(c_1060, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(B_14, A_13))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_298, c_992])).
% 4.99/2.07  tff(c_5561, plain, (![A_130]: (k2_xboole_0('#skF_2', k4_xboole_0(A_130, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_2', k4_xboole_0(A_130, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_39, c_5208])).
% 4.99/2.07  tff(c_5654, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1060, c_5561])).
% 4.99/2.07  tff(c_5706, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5413, c_2, c_3195, c_16, c_5654])).
% 4.99/2.07  tff(c_5708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_5706])).
% 4.99/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/2.07  
% 4.99/2.07  Inference rules
% 4.99/2.07  ----------------------
% 4.99/2.07  #Ref     : 0
% 4.99/2.07  #Sup     : 1449
% 4.99/2.07  #Fact    : 0
% 4.99/2.07  #Define  : 0
% 4.99/2.07  #Split   : 4
% 4.99/2.07  #Chain   : 0
% 4.99/2.07  #Close   : 0
% 4.99/2.07  
% 4.99/2.07  Ordering : KBO
% 4.99/2.07  
% 4.99/2.07  Simplification rules
% 4.99/2.07  ----------------------
% 4.99/2.07  #Subsume      : 5
% 4.99/2.07  #Demod        : 1396
% 4.99/2.07  #Tautology    : 990
% 4.99/2.07  #SimpNegUnit  : 1
% 4.99/2.07  #BackRed      : 4
% 4.99/2.07  
% 4.99/2.07  #Partial instantiations: 0
% 4.99/2.07  #Strategies tried      : 1
% 4.99/2.07  
% 4.99/2.07  Timing (in seconds)
% 4.99/2.07  ----------------------
% 4.99/2.07  Preprocessing        : 0.32
% 4.99/2.07  Parsing              : 0.17
% 4.99/2.07  CNF conversion       : 0.02
% 4.99/2.07  Main loop            : 0.92
% 4.99/2.07  Inferencing          : 0.26
% 4.99/2.07  Reduction            : 0.45
% 4.99/2.07  Demodulation         : 0.36
% 4.99/2.07  BG Simplification    : 0.03
% 4.99/2.07  Subsumption          : 0.14
% 4.99/2.07  Abstraction          : 0.04
% 4.99/2.07  MUC search           : 0.00
% 4.99/2.07  Cooper               : 0.00
% 4.99/2.07  Total                : 1.28
% 4.99/2.07  Index Insertion      : 0.00
% 4.99/2.07  Index Deletion       : 0.00
% 4.99/2.07  Index Matching       : 0.00
% 4.99/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
