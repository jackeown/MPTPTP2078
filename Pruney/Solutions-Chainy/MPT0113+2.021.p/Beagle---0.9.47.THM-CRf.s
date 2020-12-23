%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:14 EST 2020

% Result     : Theorem 13.70s
% Output     : CNFRefutation 13.76s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 151 expanded)
%              Number of leaves         :   29 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 175 expanded)
%              Number of equality atoms :   49 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_67,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_163,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_263,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2420,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k3_xboole_0(B_112,A_111)) = k4_xboole_0(A_111,B_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_263])).

tff(c_68,plain,(
    ! [B_36,A_37] : k5_xboole_0(B_36,A_37) = k5_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_84,plain,(
    ! [A_37] : k5_xboole_0(k1_xboole_0,A_37) = A_37 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_22])).

tff(c_28,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_899,plain,(
    ! [A_75,B_76,C_77] : k5_xboole_0(k5_xboole_0(A_75,B_76),C_77) = k5_xboole_0(A_75,k5_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_963,plain,(
    ! [A_28,C_77] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_77)) = k5_xboole_0(k1_xboole_0,C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_899])).

tff(c_976,plain,(
    ! [A_28,C_77] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_77)) = C_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_963])).

tff(c_10235,plain,(
    ! [A_216,B_217] : k5_xboole_0(A_216,k4_xboole_0(A_216,B_217)) = k3_xboole_0(B_217,A_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_2420,c_976])).

tff(c_32,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_250,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_258,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_250])).

tff(c_20,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1406,plain,(
    ! [A_87,B_88] : k3_xboole_0(k4_xboole_0(A_87,B_88),A_87) = k4_xboole_0(A_87,B_88) ),
    inference(resolution,[status(thm)],[c_20,c_250])).

tff(c_453,plain,(
    ! [A_59,B_60,C_61] : k3_xboole_0(k3_xboole_0(A_59,B_60),C_61) = k3_xboole_0(A_59,k3_xboole_0(B_60,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_495,plain,(
    ! [C_61] : k3_xboole_0('#skF_3',k3_xboole_0(k4_xboole_0('#skF_4','#skF_5'),C_61)) = k3_xboole_0('#skF_3',C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_453])).

tff(c_1424,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1406,c_495])).

tff(c_1484,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_2,c_1424])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1508,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1484,c_12])).

tff(c_1600,plain,(
    k5_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1508,c_976])).

tff(c_10261,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_10235,c_1600])).

tff(c_2435,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k4_xboole_0(A_111,B_112)) = k3_xboole_0(B_112,A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_2420,c_976])).

tff(c_10775,plain,(
    ! [A_224,B_225] : k3_xboole_0(A_224,k4_xboole_0(A_224,B_225)) = k4_xboole_0(A_224,B_225) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1406])).

tff(c_10960,plain,(
    ! [A_224,B_225] : k5_xboole_0(A_224,k4_xboole_0(A_224,B_225)) = k4_xboole_0(A_224,k4_xboole_0(A_224,B_225)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10775,c_12])).

tff(c_34413,plain,(
    ! [A_431,B_432] : k4_xboole_0(A_431,k4_xboole_0(A_431,B_432)) = k3_xboole_0(B_432,A_431) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2435,c_10960])).

tff(c_35014,plain,(
    ! [B_433,A_434] : r1_tarski(k3_xboole_0(B_433,A_434),A_434) ),
    inference(superposition,[status(thm),theory(equality)],[c_34413,c_20])).

tff(c_35065,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10261,c_35014])).

tff(c_35191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_35065])).

tff(c_35192,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_18,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_35314,plain,(
    ! [A_441,B_442] : k5_xboole_0(A_441,k3_xboole_0(A_441,B_442)) = k4_xboole_0(A_441,B_442) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_35346,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = k4_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_35314])).

tff(c_35354,plain,(
    ! [A_443] : k4_xboole_0(A_443,k1_xboole_0) = A_443 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_35346])).

tff(c_24,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_35363,plain,(
    ! [A_443] : r1_xboole_0(A_443,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_35354,c_24])).

tff(c_35411,plain,(
    ! [A_448,B_449,C_450] :
      ( ~ r1_xboole_0(A_448,B_449)
      | ~ r2_hidden(C_450,k3_xboole_0(A_448,B_449)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_35436,plain,(
    ! [A_19,C_450] :
      ( ~ r1_xboole_0(A_19,k1_xboole_0)
      | ~ r2_hidden(C_450,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_35411])).

tff(c_35441,plain,(
    ! [C_450] : ~ r2_hidden(C_450,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35363,c_35436])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36338,plain,(
    ! [A_474,B_475] :
      ( ~ r1_xboole_0(A_474,B_475)
      | k3_xboole_0(A_474,B_475) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_35411])).

tff(c_36353,plain,(
    ! [A_476,B_477] : k3_xboole_0(k4_xboole_0(A_476,B_477),B_477) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_36338])).

tff(c_35280,plain,(
    ! [A_439,B_440] :
      ( k3_xboole_0(A_439,B_440) = A_439
      | ~ r1_tarski(A_439,B_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_35292,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_35280])).

tff(c_36066,plain,(
    ! [A_468,B_469,C_470] : k3_xboole_0(k3_xboole_0(A_468,B_469),C_470) = k3_xboole_0(A_468,k3_xboole_0(B_469,C_470)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36111,plain,(
    ! [C_470] : k3_xboole_0('#skF_3',k3_xboole_0(k4_xboole_0('#skF_4','#skF_5'),C_470)) = k3_xboole_0('#skF_3',C_470) ),
    inference(superposition,[status(thm),theory(equality)],[c_35292,c_36066])).

tff(c_36359,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36353,c_36111])).

tff(c_36410,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_36359])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36431,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_5'),k1_xboole_0)
    | r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36410,c_6])).

tff(c_36442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35192,c_35441,c_36431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:45:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.70/6.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.70/6.70  
% 13.70/6.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.70/6.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 13.70/6.70  
% 13.70/6.70  %Foreground sorts:
% 13.70/6.70  
% 13.70/6.70  
% 13.70/6.70  %Background operators:
% 13.70/6.70  
% 13.70/6.70  
% 13.70/6.70  %Foreground operators:
% 13.70/6.70  tff('#skF_2', type, '#skF_2': $i > $i).
% 13.70/6.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.70/6.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.70/6.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.70/6.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.70/6.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.70/6.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.70/6.70  tff('#skF_5', type, '#skF_5': $i).
% 13.70/6.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.70/6.70  tff('#skF_3', type, '#skF_3': $i).
% 13.70/6.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.70/6.70  tff('#skF_4', type, '#skF_4': $i).
% 13.70/6.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.70/6.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.70/6.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.70/6.70  
% 13.76/6.72  tff(f_78, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 13.76/6.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.76/6.72  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.76/6.72  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 13.76/6.72  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 13.76/6.72  tff(f_71, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 13.76/6.72  tff(f_69, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.76/6.72  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.76/6.72  tff(f_63, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.76/6.72  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 13.76/6.72  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 13.76/6.72  tff(f_67, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 13.76/6.72  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 13.76/6.72  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 13.76/6.72  tff(c_30, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.76/6.72  tff(c_163, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_30])).
% 13.76/6.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.76/6.72  tff(c_263, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.76/6.72  tff(c_2420, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k3_xboole_0(B_112, A_111))=k4_xboole_0(A_111, B_112))), inference(superposition, [status(thm), theory('equality')], [c_2, c_263])).
% 13.76/6.72  tff(c_68, plain, (![B_36, A_37]: (k5_xboole_0(B_36, A_37)=k5_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.76/6.72  tff(c_22, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.76/6.72  tff(c_84, plain, (![A_37]: (k5_xboole_0(k1_xboole_0, A_37)=A_37)), inference(superposition, [status(thm), theory('equality')], [c_68, c_22])).
% 13.76/6.72  tff(c_28, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.76/6.72  tff(c_899, plain, (![A_75, B_76, C_77]: (k5_xboole_0(k5_xboole_0(A_75, B_76), C_77)=k5_xboole_0(A_75, k5_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.76/6.72  tff(c_963, plain, (![A_28, C_77]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_77))=k5_xboole_0(k1_xboole_0, C_77))), inference(superposition, [status(thm), theory('equality')], [c_28, c_899])).
% 13.76/6.72  tff(c_976, plain, (![A_28, C_77]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_77))=C_77)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_963])).
% 13.76/6.72  tff(c_10235, plain, (![A_216, B_217]: (k5_xboole_0(A_216, k4_xboole_0(A_216, B_217))=k3_xboole_0(B_217, A_216))), inference(superposition, [status(thm), theory('equality')], [c_2420, c_976])).
% 13.76/6.72  tff(c_32, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.76/6.72  tff(c_250, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.76/6.72  tff(c_258, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_32, c_250])).
% 13.76/6.72  tff(c_20, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.76/6.72  tff(c_1406, plain, (![A_87, B_88]: (k3_xboole_0(k4_xboole_0(A_87, B_88), A_87)=k4_xboole_0(A_87, B_88))), inference(resolution, [status(thm)], [c_20, c_250])).
% 13.76/6.72  tff(c_453, plain, (![A_59, B_60, C_61]: (k3_xboole_0(k3_xboole_0(A_59, B_60), C_61)=k3_xboole_0(A_59, k3_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.76/6.72  tff(c_495, plain, (![C_61]: (k3_xboole_0('#skF_3', k3_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), C_61))=k3_xboole_0('#skF_3', C_61))), inference(superposition, [status(thm), theory('equality')], [c_258, c_453])).
% 13.76/6.72  tff(c_1424, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1406, c_495])).
% 13.76/6.72  tff(c_1484, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_258, c_2, c_1424])).
% 13.76/6.72  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.76/6.72  tff(c_1508, plain, (k5_xboole_0('#skF_4', '#skF_3')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1484, c_12])).
% 13.76/6.72  tff(c_1600, plain, (k5_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1508, c_976])).
% 13.76/6.72  tff(c_10261, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_10235, c_1600])).
% 13.76/6.72  tff(c_2435, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k4_xboole_0(A_111, B_112))=k3_xboole_0(B_112, A_111))), inference(superposition, [status(thm), theory('equality')], [c_2420, c_976])).
% 13.76/6.72  tff(c_10775, plain, (![A_224, B_225]: (k3_xboole_0(A_224, k4_xboole_0(A_224, B_225))=k4_xboole_0(A_224, B_225))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1406])).
% 13.76/6.72  tff(c_10960, plain, (![A_224, B_225]: (k5_xboole_0(A_224, k4_xboole_0(A_224, B_225))=k4_xboole_0(A_224, k4_xboole_0(A_224, B_225)))), inference(superposition, [status(thm), theory('equality')], [c_10775, c_12])).
% 13.76/6.72  tff(c_34413, plain, (![A_431, B_432]: (k4_xboole_0(A_431, k4_xboole_0(A_431, B_432))=k3_xboole_0(B_432, A_431))), inference(demodulation, [status(thm), theory('equality')], [c_2435, c_10960])).
% 13.76/6.72  tff(c_35014, plain, (![B_433, A_434]: (r1_tarski(k3_xboole_0(B_433, A_434), A_434))), inference(superposition, [status(thm), theory('equality')], [c_34413, c_20])).
% 13.76/6.72  tff(c_35065, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10261, c_35014])).
% 13.76/6.72  tff(c_35191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_35065])).
% 13.76/6.72  tff(c_35192, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 13.76/6.72  tff(c_18, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.76/6.72  tff(c_35314, plain, (![A_441, B_442]: (k5_xboole_0(A_441, k3_xboole_0(A_441, B_442))=k4_xboole_0(A_441, B_442))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.76/6.72  tff(c_35346, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=k4_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_35314])).
% 13.76/6.72  tff(c_35354, plain, (![A_443]: (k4_xboole_0(A_443, k1_xboole_0)=A_443)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_35346])).
% 13.76/6.72  tff(c_24, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.76/6.72  tff(c_35363, plain, (![A_443]: (r1_xboole_0(A_443, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_35354, c_24])).
% 13.76/6.72  tff(c_35411, plain, (![A_448, B_449, C_450]: (~r1_xboole_0(A_448, B_449) | ~r2_hidden(C_450, k3_xboole_0(A_448, B_449)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.76/6.72  tff(c_35436, plain, (![A_19, C_450]: (~r1_xboole_0(A_19, k1_xboole_0) | ~r2_hidden(C_450, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_35411])).
% 13.76/6.72  tff(c_35441, plain, (![C_450]: (~r2_hidden(C_450, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_35363, c_35436])).
% 13.76/6.72  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.76/6.72  tff(c_36338, plain, (![A_474, B_475]: (~r1_xboole_0(A_474, B_475) | k3_xboole_0(A_474, B_475)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_35411])).
% 13.76/6.72  tff(c_36353, plain, (![A_476, B_477]: (k3_xboole_0(k4_xboole_0(A_476, B_477), B_477)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_36338])).
% 13.76/6.72  tff(c_35280, plain, (![A_439, B_440]: (k3_xboole_0(A_439, B_440)=A_439 | ~r1_tarski(A_439, B_440))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.76/6.72  tff(c_35292, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_32, c_35280])).
% 13.76/6.72  tff(c_36066, plain, (![A_468, B_469, C_470]: (k3_xboole_0(k3_xboole_0(A_468, B_469), C_470)=k3_xboole_0(A_468, k3_xboole_0(B_469, C_470)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.76/6.72  tff(c_36111, plain, (![C_470]: (k3_xboole_0('#skF_3', k3_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), C_470))=k3_xboole_0('#skF_3', C_470))), inference(superposition, [status(thm), theory('equality')], [c_35292, c_36066])).
% 13.76/6.72  tff(c_36359, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36353, c_36111])).
% 13.76/6.72  tff(c_36410, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_36359])).
% 13.76/6.72  tff(c_6, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.76/6.72  tff(c_36431, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_5'), k1_xboole_0) | r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36410, c_6])).
% 13.76/6.72  tff(c_36442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35192, c_35441, c_36431])).
% 13.76/6.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.76/6.72  
% 13.76/6.72  Inference rules
% 13.76/6.72  ----------------------
% 13.76/6.72  #Ref     : 0
% 13.76/6.72  #Sup     : 9266
% 13.76/6.72  #Fact    : 0
% 13.76/6.72  #Define  : 0
% 13.76/6.72  #Split   : 8
% 13.76/6.72  #Chain   : 0
% 13.76/6.72  #Close   : 0
% 13.76/6.72  
% 13.76/6.72  Ordering : KBO
% 13.76/6.72  
% 13.76/6.72  Simplification rules
% 13.76/6.72  ----------------------
% 13.76/6.72  #Subsume      : 408
% 13.76/6.72  #Demod        : 8867
% 13.76/6.72  #Tautology    : 5584
% 13.76/6.72  #SimpNegUnit  : 134
% 13.76/6.72  #BackRed      : 1
% 13.76/6.72  
% 13.76/6.72  #Partial instantiations: 0
% 13.76/6.72  #Strategies tried      : 1
% 13.76/6.72  
% 13.76/6.72  Timing (in seconds)
% 13.76/6.72  ----------------------
% 13.76/6.72  Preprocessing        : 0.44
% 13.76/6.72  Parsing              : 0.24
% 13.76/6.72  CNF conversion       : 0.03
% 13.76/6.72  Main loop            : 5.36
% 13.76/6.72  Inferencing          : 0.92
% 13.76/6.72  Reduction            : 3.22
% 13.76/6.72  Demodulation         : 2.90
% 13.76/6.72  BG Simplification    : 0.11
% 13.76/6.72  Subsumption          : 0.86
% 13.76/6.72  Abstraction          : 0.14
% 13.76/6.72  MUC search           : 0.00
% 13.76/6.72  Cooper               : 0.00
% 13.76/6.72  Total                : 5.84
% 13.76/6.72  Index Insertion      : 0.00
% 13.76/6.72  Index Deletion       : 0.00
% 13.76/6.72  Index Matching       : 0.00
% 13.76/6.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
