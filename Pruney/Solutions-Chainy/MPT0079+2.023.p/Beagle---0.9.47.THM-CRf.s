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
% DateTime   : Thu Dec  3 09:43:45 EST 2020

% Result     : Theorem 10.67s
% Output     : CNFRefutation 10.67s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 283 expanded)
%              Number of leaves         :   30 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 355 expanded)
%              Number of equality atoms :   66 ( 250 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1445,plain,(
    ! [A_91,B_92,C_93] :
      ( ~ r1_xboole_0(A_91,B_92)
      | ~ r2_hidden(C_93,k3_xboole_0(A_91,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2242,plain,(
    ! [A_112,B_113] :
      ( ~ r1_xboole_0(A_112,B_113)
      | k3_xboole_0(A_112,B_113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_1445])).

tff(c_2259,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_2242])).

tff(c_32,plain,(
    ! [A_29,B_30] : k2_xboole_0(k3_xboole_0(A_29,B_30),k4_xboole_0(A_29,B_30)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2288,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_6','#skF_4')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2259,c_32])).

tff(c_83,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_111,plain,(
    ! [A_42] : k2_xboole_0(k1_xboole_0,A_42) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_16])).

tff(c_2767,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2288,c_111])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_45,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_130,plain,(
    k2_xboole_0('#skF_6','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_83])).

tff(c_36,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_313,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_384,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k2_xboole_0(A_57,B_58)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_313])).

tff(c_397,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_384])).

tff(c_2314,plain,(
    ! [A_114,B_115,C_116] : k4_xboole_0(k4_xboole_0(A_114,B_115),C_116) = k4_xboole_0(A_114,k2_xboole_0(B_115,C_116)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_23799,plain,(
    ! [C_330,A_331,B_332] : k2_xboole_0(C_330,k4_xboole_0(A_331,k2_xboole_0(B_332,C_330))) = k2_xboole_0(C_330,k4_xboole_0(A_331,B_332)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2314,c_20])).

tff(c_24129,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_6','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_23799])).

tff(c_24249,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2767,c_16,c_24129])).

tff(c_22,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2260,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_2242])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_858,plain,(
    ! [A_72,B_73] : k2_xboole_0(k3_xboole_0(A_72,B_73),k4_xboole_0(A_72,B_73)) = A_72 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2928,plain,(
    ! [A_119,B_120] : k2_xboole_0(k3_xboole_0(A_119,B_120),k4_xboole_0(B_120,A_119)) = B_120 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_858])).

tff(c_2992,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2260,c_2928])).

tff(c_423,plain,(
    ! [A_59,B_60] : k4_xboole_0(k2_xboole_0(A_59,B_60),B_60) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_445,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_423])).

tff(c_3112,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_5'),k1_xboole_0) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2992,c_445])).

tff(c_3154,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_3112])).

tff(c_403,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_384])).

tff(c_24555,plain,(
    ! [A_333] : k2_xboole_0('#skF_6',k4_xboole_0(A_333,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_6',k4_xboole_0(A_333,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_23799])).

tff(c_24724,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_24555])).

tff(c_24780,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24249,c_2,c_3154,c_16,c_24724])).

tff(c_2998,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2259,c_2928])).

tff(c_3213,plain,(
    k4_xboole_0(k4_xboole_0('#skF_4','#skF_6'),k1_xboole_0) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2998,c_445])).

tff(c_3255,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_3213])).

tff(c_24835,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24780,c_3255])).

tff(c_24,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_xboole_0(A_19,B_20),B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_341,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_313])).

tff(c_989,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1035,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_989])).

tff(c_1059,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = A_33 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1035])).

tff(c_2608,plain,(
    ! [A_117,B_118] : k4_xboole_0(k2_xboole_0(A_117,B_118),A_117) = k4_xboole_0(B_118,A_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_423])).

tff(c_28,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2623,plain,(
    ! [A_117,B_118] : k4_xboole_0(k2_xboole_0(A_117,B_118),k4_xboole_0(B_118,A_117)) = k3_xboole_0(k2_xboole_0(A_117,B_118),A_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_2608,c_28])).

tff(c_10082,plain,(
    ! [A_225,B_226] : k4_xboole_0(k2_xboole_0(A_225,B_226),k4_xboole_0(B_226,A_225)) = A_225 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_4,c_2623])).

tff(c_10286,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k4_xboole_0('#skF_6','#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_10082])).

tff(c_24816,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k4_xboole_0('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24780,c_10286])).

tff(c_24857,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3154,c_24816])).

tff(c_25435,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24835,c_24857])).

tff(c_25437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_25435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.67/4.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.67/4.20  
% 10.67/4.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.67/4.20  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 10.67/4.20  
% 10.67/4.20  %Foreground sorts:
% 10.67/4.20  
% 10.67/4.20  
% 10.67/4.20  %Background operators:
% 10.67/4.20  
% 10.67/4.20  
% 10.67/4.20  %Foreground operators:
% 10.67/4.20  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.67/4.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.67/4.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.67/4.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.67/4.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.67/4.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.67/4.20  tff('#skF_5', type, '#skF_5': $i).
% 10.67/4.20  tff('#skF_6', type, '#skF_6': $i).
% 10.67/4.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.67/4.20  tff('#skF_3', type, '#skF_3': $i).
% 10.67/4.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.67/4.20  tff('#skF_4', type, '#skF_4': $i).
% 10.67/4.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.67/4.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.67/4.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.67/4.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.67/4.20  
% 10.67/4.22  tff(f_86, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 10.67/4.22  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.67/4.22  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.67/4.22  tff(f_73, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 10.67/4.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.67/4.22  tff(f_57, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 10.67/4.22  tff(f_77, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.67/4.22  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.67/4.22  tff(f_67, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.67/4.22  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.67/4.22  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 10.67/4.22  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.67/4.22  tff(f_65, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 10.67/4.22  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.67/4.22  tff(c_38, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.67/4.22  tff(c_40, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.67/4.22  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.67/4.22  tff(c_1445, plain, (![A_91, B_92, C_93]: (~r1_xboole_0(A_91, B_92) | ~r2_hidden(C_93, k3_xboole_0(A_91, B_92)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.67/4.22  tff(c_2242, plain, (![A_112, B_113]: (~r1_xboole_0(A_112, B_113) | k3_xboole_0(A_112, B_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1445])).
% 10.67/4.22  tff(c_2259, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_2242])).
% 10.67/4.22  tff(c_32, plain, (![A_29, B_30]: (k2_xboole_0(k3_xboole_0(A_29, B_30), k4_xboole_0(A_29, B_30))=A_29)), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.67/4.22  tff(c_2288, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_6', '#skF_4'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2259, c_32])).
% 10.67/4.22  tff(c_83, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.67/4.22  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.67/4.22  tff(c_111, plain, (![A_42]: (k2_xboole_0(k1_xboole_0, A_42)=A_42)), inference(superposition, [status(thm), theory('equality')], [c_83, c_16])).
% 10.67/4.22  tff(c_2767, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2288, c_111])).
% 10.67/4.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.67/4.22  tff(c_44, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.67/4.22  tff(c_45, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 10.67/4.22  tff(c_130, plain, (k2_xboole_0('#skF_6', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_45, c_83])).
% 10.67/4.22  tff(c_36, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.67/4.22  tff(c_313, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.67/4.22  tff(c_384, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k2_xboole_0(A_57, B_58))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_313])).
% 10.67/4.22  tff(c_397, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_130, c_384])).
% 10.67/4.22  tff(c_2314, plain, (![A_114, B_115, C_116]: (k4_xboole_0(k4_xboole_0(A_114, B_115), C_116)=k4_xboole_0(A_114, k2_xboole_0(B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.67/4.22  tff(c_20, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.67/4.22  tff(c_23799, plain, (![C_330, A_331, B_332]: (k2_xboole_0(C_330, k4_xboole_0(A_331, k2_xboole_0(B_332, C_330)))=k2_xboole_0(C_330, k4_xboole_0(A_331, B_332)))), inference(superposition, [status(thm), theory('equality')], [c_2314, c_20])).
% 10.67/4.22  tff(c_24129, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_397, c_23799])).
% 10.67/4.22  tff(c_24249, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2767, c_16, c_24129])).
% 10.67/4.22  tff(c_22, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.67/4.22  tff(c_42, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.67/4.22  tff(c_2260, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_2242])).
% 10.67/4.22  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.67/4.22  tff(c_858, plain, (![A_72, B_73]: (k2_xboole_0(k3_xboole_0(A_72, B_73), k4_xboole_0(A_72, B_73))=A_72)), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.67/4.22  tff(c_2928, plain, (![A_119, B_120]: (k2_xboole_0(k3_xboole_0(A_119, B_120), k4_xboole_0(B_120, A_119))=B_120)), inference(superposition, [status(thm), theory('equality')], [c_4, c_858])).
% 10.67/4.22  tff(c_2992, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2260, c_2928])).
% 10.67/4.22  tff(c_423, plain, (![A_59, B_60]: (k4_xboole_0(k2_xboole_0(A_59, B_60), B_60)=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.67/4.22  tff(c_445, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_423])).
% 10.67/4.22  tff(c_3112, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_5'), k1_xboole_0)=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2992, c_445])).
% 10.67/4.22  tff(c_3154, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_3112])).
% 10.67/4.22  tff(c_403, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_384])).
% 10.67/4.22  tff(c_24555, plain, (![A_333]: (k2_xboole_0('#skF_6', k4_xboole_0(A_333, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_6', k4_xboole_0(A_333, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_45, c_23799])).
% 10.67/4.22  tff(c_24724, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_403, c_24555])).
% 10.67/4.22  tff(c_24780, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24249, c_2, c_3154, c_16, c_24724])).
% 10.67/4.22  tff(c_2998, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2259, c_2928])).
% 10.67/4.22  tff(c_3213, plain, (k4_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), k1_xboole_0)=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2998, c_445])).
% 10.67/4.22  tff(c_3255, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_3213])).
% 10.67/4.22  tff(c_24835, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24780, c_3255])).
% 10.67/4.22  tff(c_24, plain, (![A_19, B_20]: (k4_xboole_0(k2_xboole_0(A_19, B_20), B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.67/4.22  tff(c_341, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(A_33, B_34))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_313])).
% 10.67/4.22  tff(c_989, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.67/4.22  tff(c_1035, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k2_xboole_0(A_33, B_34))=k4_xboole_0(A_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_341, c_989])).
% 10.67/4.22  tff(c_1059, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k2_xboole_0(A_33, B_34))=A_33)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1035])).
% 10.67/4.22  tff(c_2608, plain, (![A_117, B_118]: (k4_xboole_0(k2_xboole_0(A_117, B_118), A_117)=k4_xboole_0(B_118, A_117))), inference(superposition, [status(thm), theory('equality')], [c_2, c_423])).
% 10.67/4.22  tff(c_28, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.67/4.22  tff(c_2623, plain, (![A_117, B_118]: (k4_xboole_0(k2_xboole_0(A_117, B_118), k4_xboole_0(B_118, A_117))=k3_xboole_0(k2_xboole_0(A_117, B_118), A_117))), inference(superposition, [status(thm), theory('equality')], [c_2608, c_28])).
% 10.67/4.22  tff(c_10082, plain, (![A_225, B_226]: (k4_xboole_0(k2_xboole_0(A_225, B_226), k4_xboole_0(B_226, A_225))=A_225)), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_4, c_2623])).
% 10.67/4.22  tff(c_10286, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k4_xboole_0('#skF_6', '#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_45, c_10082])).
% 10.67/4.22  tff(c_24816, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k4_xboole_0('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24780, c_10286])).
% 10.67/4.22  tff(c_24857, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3154, c_24816])).
% 10.67/4.22  tff(c_25435, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24835, c_24857])).
% 10.67/4.22  tff(c_25437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_25435])).
% 10.67/4.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.67/4.22  
% 10.67/4.22  Inference rules
% 10.67/4.22  ----------------------
% 10.67/4.22  #Ref     : 0
% 10.67/4.22  #Sup     : 6424
% 10.67/4.22  #Fact    : 0
% 10.67/4.22  #Define  : 0
% 10.67/4.22  #Split   : 1
% 10.67/4.22  #Chain   : 0
% 10.67/4.22  #Close   : 0
% 10.67/4.22  
% 10.67/4.22  Ordering : KBO
% 10.67/4.22  
% 10.67/4.22  Simplification rules
% 10.67/4.22  ----------------------
% 10.67/4.22  #Subsume      : 116
% 10.67/4.22  #Demod        : 6805
% 10.67/4.22  #Tautology    : 4231
% 10.67/4.22  #SimpNegUnit  : 51
% 10.67/4.22  #BackRed      : 68
% 10.67/4.22  
% 10.67/4.22  #Partial instantiations: 0
% 10.67/4.22  #Strategies tried      : 1
% 10.67/4.22  
% 10.67/4.22  Timing (in seconds)
% 10.67/4.22  ----------------------
% 10.95/4.22  Preprocessing        : 0.30
% 10.95/4.22  Parsing              : 0.16
% 10.95/4.22  CNF conversion       : 0.02
% 10.95/4.22  Main loop            : 3.15
% 10.95/4.22  Inferencing          : 0.55
% 10.95/4.22  Reduction            : 1.83
% 10.95/4.22  Demodulation         : 1.63
% 10.95/4.22  BG Simplification    : 0.07
% 10.95/4.22  Subsumption          : 0.52
% 10.95/4.22  Abstraction          : 0.09
% 10.95/4.22  MUC search           : 0.00
% 10.95/4.22  Cooper               : 0.00
% 10.95/4.22  Total                : 3.49
% 10.95/4.22  Index Insertion      : 0.00
% 10.95/4.22  Index Deletion       : 0.00
% 10.95/4.22  Index Matching       : 0.00
% 10.95/4.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
