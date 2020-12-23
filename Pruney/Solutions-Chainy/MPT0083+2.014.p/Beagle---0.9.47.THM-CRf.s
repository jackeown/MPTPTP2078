%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:03 EST 2020

% Result     : Theorem 6.24s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 101 expanded)
%              Number of leaves         :   25 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   68 ( 108 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_113,plain,(
    ! [A_43] : k3_xboole_0(k1_xboole_0,A_43) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_14])).

tff(c_451,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_472,plain,(
    ! [A_43] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_451])).

tff(c_488,plain,(
    ! [A_43] : k4_xboole_0(k1_xboole_0,A_43) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_472])).

tff(c_34,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_53,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(B_35,A_36)
      | ~ r1_xboole_0(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_243,plain,(
    ! [A_49,B_50,C_51] :
      ( ~ r1_xboole_0(A_49,B_50)
      | ~ r2_hidden(C_51,k3_xboole_0(A_49,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_272,plain,(
    ! [A_53,B_54] :
      ( ~ r1_xboole_0(A_53,B_54)
      | k3_xboole_0(A_53,B_54) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_243])).

tff(c_285,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_272])).

tff(c_565,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k3_xboole_0(A_65,B_66),C_67) = k3_xboole_0(A_65,k4_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_611,plain,(
    ! [C_67] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_3',C_67)) = k4_xboole_0(k1_xboole_0,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_565])).

tff(c_752,plain,(
    ! [C_71] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_3',C_71)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_611])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_760,plain,(
    ! [C_71] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_3',C_71)) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_18])).

tff(c_1548,plain,(
    ! [C_91] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_3',C_91)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_760])).

tff(c_1578,plain,(
    ! [B_19] : k4_xboole_0('#skF_4',k3_xboole_0('#skF_3',B_19)) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1548])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k3_xboole_0(A_20,B_21),C_22) = k3_xboole_0(A_20,k4_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_29] : r1_xboole_0(A_29,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_259,plain,(
    ! [A_14,C_51] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_51,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_243])).

tff(c_264,plain,(
    ! [C_51] : ~ r2_hidden(C_51,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_259])).

tff(c_351,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_366,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_351])).

tff(c_369,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_366])).

tff(c_457,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,k3_xboole_0(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_20])).

tff(c_483,plain,(
    ! [A_60,B_61] : k3_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_457])).

tff(c_3108,plain,(
    ! [B_113,A_114] : k4_xboole_0(B_113,k3_xboole_0(A_114,B_113)) = k4_xboole_0(B_113,A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_451])).

tff(c_3199,plain,(
    ! [A_60,B_61] : k4_xboole_0(k3_xboole_0(A_60,B_61),k3_xboole_0(A_60,B_61)) = k4_xboole_0(k3_xboole_0(A_60,B_61),A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_3108])).

tff(c_3313,plain,(
    ! [A_115,B_116] : k3_xboole_0(A_115,k4_xboole_0(B_116,A_115)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_369,c_3199])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3357,plain,(
    ! [A_115,B_116] :
      ( r2_hidden('#skF_1'(A_115,k4_xboole_0(B_116,A_115)),k1_xboole_0)
      | r1_xboole_0(A_115,k4_xboole_0(B_116,A_115)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3313,c_6])).

tff(c_3498,plain,(
    ! [A_117,B_118] : r1_xboole_0(A_117,k4_xboole_0(B_118,A_117)) ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_3357])).

tff(c_5459,plain,(
    ! [C_141,A_142,B_143] : r1_xboole_0(C_141,k3_xboole_0(A_142,k4_xboole_0(B_143,C_141))) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3498])).

tff(c_5755,plain,(
    ! [C_148,B_149,A_150] : r1_xboole_0(C_148,k3_xboole_0(k4_xboole_0(B_149,C_148),A_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5459])).

tff(c_5800,plain,(
    ! [B_19,A_150] : r1_xboole_0(k3_xboole_0('#skF_3',B_19),k3_xboole_0('#skF_4',A_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1578,c_5755])).

tff(c_32,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_5','#skF_3'),k3_xboole_0('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_35,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_32])).

tff(c_11292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5800,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:22:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.24/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.37  
% 6.24/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.37  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 6.24/2.37  
% 6.24/2.37  %Foreground sorts:
% 6.24/2.37  
% 6.24/2.37  
% 6.24/2.37  %Background operators:
% 6.24/2.37  
% 6.24/2.37  
% 6.24/2.37  %Foreground operators:
% 6.24/2.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.24/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.24/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.24/2.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.24/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.24/2.37  tff('#skF_5', type, '#skF_5': $i).
% 6.24/2.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.24/2.37  tff('#skF_3', type, '#skF_3': $i).
% 6.24/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.24/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.24/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.24/2.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.24/2.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.24/2.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.24/2.37  
% 6.55/2.38  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.55/2.38  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.55/2.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.55/2.38  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.55/2.38  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.55/2.38  tff(f_82, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 6.55/2.38  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.55/2.38  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.55/2.38  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.55/2.38  tff(f_65, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.55/2.38  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.55/2.38  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.55/2.38  tff(c_16, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.55/2.38  tff(c_91, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.55/2.38  tff(c_14, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.55/2.38  tff(c_113, plain, (![A_43]: (k3_xboole_0(k1_xboole_0, A_43)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_91, c_14])).
% 6.55/2.38  tff(c_451, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.55/2.38  tff(c_472, plain, (![A_43]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_43))), inference(superposition, [status(thm), theory('equality')], [c_113, c_451])).
% 6.55/2.38  tff(c_488, plain, (![A_43]: (k4_xboole_0(k1_xboole_0, A_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_472])).
% 6.55/2.38  tff(c_34, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.55/2.38  tff(c_53, plain, (![B_35, A_36]: (r1_xboole_0(B_35, A_36) | ~r1_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.55/2.38  tff(c_59, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_53])).
% 6.55/2.38  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.55/2.38  tff(c_243, plain, (![A_49, B_50, C_51]: (~r1_xboole_0(A_49, B_50) | ~r2_hidden(C_51, k3_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.55/2.38  tff(c_272, plain, (![A_53, B_54]: (~r1_xboole_0(A_53, B_54) | k3_xboole_0(A_53, B_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_243])).
% 6.55/2.38  tff(c_285, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_59, c_272])).
% 6.55/2.38  tff(c_565, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k3_xboole_0(A_65, B_66), C_67)=k3_xboole_0(A_65, k4_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.55/2.38  tff(c_611, plain, (![C_67]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_3', C_67))=k4_xboole_0(k1_xboole_0, C_67))), inference(superposition, [status(thm), theory('equality')], [c_285, c_565])).
% 6.55/2.38  tff(c_752, plain, (![C_71]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_3', C_71))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_488, c_611])).
% 6.55/2.38  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.55/2.38  tff(c_760, plain, (![C_71]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_3', C_71))=k4_xboole_0('#skF_4', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_752, c_18])).
% 6.55/2.38  tff(c_1548, plain, (![C_91]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_3', C_91))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_760])).
% 6.55/2.38  tff(c_1578, plain, (![B_19]: (k4_xboole_0('#skF_4', k3_xboole_0('#skF_3', B_19))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20, c_1548])).
% 6.55/2.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.55/2.38  tff(c_22, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k3_xboole_0(A_20, B_21), C_22)=k3_xboole_0(A_20, k4_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.55/2.38  tff(c_28, plain, (![A_29]: (r1_xboole_0(A_29, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.55/2.38  tff(c_259, plain, (![A_14, C_51]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_243])).
% 6.55/2.38  tff(c_264, plain, (![C_51]: (~r2_hidden(C_51, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_259])).
% 6.55/2.38  tff(c_351, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.55/2.38  tff(c_366, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_351])).
% 6.55/2.38  tff(c_369, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_366])).
% 6.55/2.38  tff(c_457, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k3_xboole_0(A_60, k3_xboole_0(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_451, c_20])).
% 6.55/2.38  tff(c_483, plain, (![A_60, B_61]: (k3_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_457])).
% 6.55/2.38  tff(c_3108, plain, (![B_113, A_114]: (k4_xboole_0(B_113, k3_xboole_0(A_114, B_113))=k4_xboole_0(B_113, A_114))), inference(superposition, [status(thm), theory('equality')], [c_2, c_451])).
% 6.55/2.38  tff(c_3199, plain, (![A_60, B_61]: (k4_xboole_0(k3_xboole_0(A_60, B_61), k3_xboole_0(A_60, B_61))=k4_xboole_0(k3_xboole_0(A_60, B_61), A_60))), inference(superposition, [status(thm), theory('equality')], [c_483, c_3108])).
% 6.55/2.38  tff(c_3313, plain, (![A_115, B_116]: (k3_xboole_0(A_115, k4_xboole_0(B_116, A_115))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_369, c_3199])).
% 6.55/2.38  tff(c_6, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.55/2.38  tff(c_3357, plain, (![A_115, B_116]: (r2_hidden('#skF_1'(A_115, k4_xboole_0(B_116, A_115)), k1_xboole_0) | r1_xboole_0(A_115, k4_xboole_0(B_116, A_115)))), inference(superposition, [status(thm), theory('equality')], [c_3313, c_6])).
% 6.55/2.38  tff(c_3498, plain, (![A_117, B_118]: (r1_xboole_0(A_117, k4_xboole_0(B_118, A_117)))), inference(negUnitSimplification, [status(thm)], [c_264, c_3357])).
% 6.55/2.38  tff(c_5459, plain, (![C_141, A_142, B_143]: (r1_xboole_0(C_141, k3_xboole_0(A_142, k4_xboole_0(B_143, C_141))))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3498])).
% 6.55/2.38  tff(c_5755, plain, (![C_148, B_149, A_150]: (r1_xboole_0(C_148, k3_xboole_0(k4_xboole_0(B_149, C_148), A_150)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5459])).
% 6.55/2.38  tff(c_5800, plain, (![B_19, A_150]: (r1_xboole_0(k3_xboole_0('#skF_3', B_19), k3_xboole_0('#skF_4', A_150)))), inference(superposition, [status(thm), theory('equality')], [c_1578, c_5755])).
% 6.55/2.38  tff(c_32, plain, (~r1_xboole_0(k3_xboole_0('#skF_5', '#skF_3'), k3_xboole_0('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.55/2.38  tff(c_35, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_32])).
% 6.55/2.38  tff(c_11292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5800, c_35])).
% 6.55/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.55/2.38  
% 6.55/2.38  Inference rules
% 6.55/2.38  ----------------------
% 6.55/2.38  #Ref     : 0
% 6.55/2.38  #Sup     : 2775
% 6.55/2.38  #Fact    : 0
% 6.55/2.38  #Define  : 0
% 6.55/2.38  #Split   : 0
% 6.55/2.38  #Chain   : 0
% 6.55/2.38  #Close   : 0
% 6.55/2.38  
% 6.55/2.38  Ordering : KBO
% 6.55/2.38  
% 6.55/2.38  Simplification rules
% 6.55/2.38  ----------------------
% 6.55/2.38  #Subsume      : 61
% 6.55/2.38  #Demod        : 2707
% 6.55/2.38  #Tautology    : 2006
% 6.55/2.38  #SimpNegUnit  : 40
% 6.55/2.38  #BackRed      : 3
% 6.55/2.38  
% 6.55/2.38  #Partial instantiations: 0
% 6.55/2.38  #Strategies tried      : 1
% 6.55/2.38  
% 6.55/2.38  Timing (in seconds)
% 6.55/2.38  ----------------------
% 6.55/2.39  Preprocessing        : 0.30
% 6.55/2.39  Parsing              : 0.16
% 6.55/2.39  CNF conversion       : 0.02
% 6.55/2.39  Main loop            : 1.33
% 6.55/2.39  Inferencing          : 0.36
% 6.55/2.39  Reduction            : 0.65
% 6.55/2.39  Demodulation         : 0.54
% 6.55/2.39  BG Simplification    : 0.04
% 6.55/2.39  Subsumption          : 0.21
% 6.55/2.39  Abstraction          : 0.06
% 6.55/2.39  MUC search           : 0.00
% 6.55/2.39  Cooper               : 0.00
% 6.55/2.39  Total                : 1.66
% 6.55/2.39  Index Insertion      : 0.00
% 6.55/2.39  Index Deletion       : 0.00
% 6.55/2.39  Index Matching       : 0.00
% 6.55/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
