%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:19 EST 2020

% Result     : Theorem 9.63s
% Output     : CNFRefutation 9.63s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 239 expanded)
%              Number of leaves         :   33 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  136 ( 471 expanded)
%              Number of equality atoms :   55 ( 202 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_8 > #skF_9 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_82,axiom,(
    ! [A] :
      ( r2_hidden(k1_xboole_0,A)
     => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_74,axiom,(
    ! [A] : r1_tarski(k1_setfam_1(A),k3_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_setfam_1)).

tff(c_80,plain,(
    k1_setfam_1(k1_tarski('#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [D_24,A_19] : r2_hidden(D_24,k2_tarski(A_19,D_24)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ! [D_24,B_20] : r2_hidden(D_24,k2_tarski(D_24,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_123,plain,(
    ! [A_51] :
      ( k1_setfam_1(A_51) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_137,plain,(
    ! [B_20] : k1_setfam_1(k2_tarski(k1_xboole_0,B_20)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_123])).

tff(c_210,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k1_setfam_1(B_58),A_59)
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_279,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k1_xboole_0,A_73)
      | ~ r2_hidden(A_73,k2_tarski(k1_xboole_0,B_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_210])).

tff(c_297,plain,(
    ! [D_24] : r1_tarski(k1_xboole_0,D_24) ),
    inference(resolution,[status(thm)],[c_46,c_279])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8899,plain,(
    ! [A_3742,B_3743,C_3744] :
      ( ~ r2_hidden('#skF_2'(A_3742,B_3743,C_3744),C_3744)
      | r2_hidden('#skF_3'(A_3742,B_3743,C_3744),C_3744)
      | k4_xboole_0(A_3742,B_3743) = C_3744 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8963,plain,(
    ! [A_3749,B_3750] :
      ( r2_hidden('#skF_3'(A_3749,B_3750,A_3749),A_3749)
      | k4_xboole_0(A_3749,B_3750) = A_3749 ) ),
    inference(resolution,[status(thm)],[c_24,c_8899])).

tff(c_227,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_1'(A_61,B_62),A_61)
      | r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_429,plain,(
    ! [A_97,B_98] :
      ( '#skF_1'(k1_tarski(A_97),B_98) = A_97
      | r1_tarski(k1_tarski(A_97),B_98) ) ),
    inference(resolution,[status(thm)],[c_227,c_32])).

tff(c_323,plain,(
    ! [D_78] : r1_tarski(k1_xboole_0,D_78) ),
    inference(resolution,[status(thm)],[c_46,c_279])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_326,plain,(
    ! [D_78] :
      ( k1_xboole_0 = D_78
      | ~ r1_tarski(D_78,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_323,c_26])).

tff(c_463,plain,(
    ! [A_101] :
      ( k1_tarski(A_101) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_101),k1_xboole_0) = A_101 ) ),
    inference(resolution,[status(thm)],[c_429,c_326])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_551,plain,(
    ! [A_107] :
      ( ~ r2_hidden(A_107,k1_xboole_0)
      | r1_tarski(k1_tarski(A_107),k1_xboole_0)
      | k1_tarski(A_107) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_4])).

tff(c_561,plain,(
    ! [A_107] :
      ( ~ r2_hidden(A_107,k1_xboole_0)
      | k1_tarski(A_107) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_551,c_326])).

tff(c_9029,plain,(
    ! [B_3753] :
      ( k1_tarski('#skF_3'(k1_xboole_0,B_3753,k1_xboole_0)) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,B_3753) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8963,c_561])).

tff(c_361,plain,(
    ! [C_83,B_84,A_85] :
      ( r2_hidden(C_83,B_84)
      | ~ r2_hidden(C_83,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_373,plain,(
    ! [C_18,B_84] :
      ( r2_hidden(C_18,B_84)
      | ~ r1_tarski(k1_tarski(C_18),B_84) ) ),
    inference(resolution,[status(thm)],[c_34,c_361])).

tff(c_9055,plain,(
    ! [B_3753,B_84] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_3753,k1_xboole_0),B_84)
      | ~ r1_tarski(k1_xboole_0,B_84)
      | k4_xboole_0(k1_xboole_0,B_3753) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9029,c_373])).

tff(c_9076,plain,(
    ! [B_3753,B_84] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_3753,k1_xboole_0),B_84)
      | k4_xboole_0(k1_xboole_0,B_3753) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_9055])).

tff(c_9164,plain,(
    ! [B_3759,B_3760] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_3759,k1_xboole_0),B_3760)
      | k4_xboole_0(k1_xboole_0,B_3759) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_9055])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12501,plain,(
    ! [B_14117,B_14118] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_14117,k1_xboole_0),B_14118)
      | k4_xboole_0(k1_xboole_0,B_14117) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9164,c_10])).

tff(c_12630,plain,(
    ! [B_14391] : k4_xboole_0(k1_xboole_0,B_14391) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9076,c_12501])).

tff(c_12854,plain,(
    ! [D_14806,B_14807] :
      ( ~ r2_hidden(D_14806,B_14807)
      | ~ r2_hidden(D_14806,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12630,c_10])).

tff(c_12897,plain,(
    ! [D_24] : ~ r2_hidden(D_24,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_46,c_12854])).

tff(c_68,plain,(
    ! [A_31] : k3_tarski(k1_tarski(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_565,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_8'(A_108,B_109),A_108)
      | r1_tarski(B_109,k1_setfam_1(A_108))
      | k1_xboole_0 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_15215,plain,(
    ! [A_20310,B_20311] :
      ( '#skF_8'(k1_tarski(A_20310),B_20311) = A_20310
      | r1_tarski(B_20311,k1_setfam_1(k1_tarski(A_20310)))
      | k1_tarski(A_20310) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_565,c_32])).

tff(c_70,plain,(
    ! [A_32] : r1_tarski(k1_setfam_1(A_32),k3_tarski(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_245,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_262,plain,(
    ! [A_32] :
      ( k3_tarski(A_32) = k1_setfam_1(A_32)
      | ~ r1_tarski(k3_tarski(A_32),k1_setfam_1(A_32)) ) ),
    inference(resolution,[status(thm)],[c_70,c_245])).

tff(c_15234,plain,(
    ! [A_20310] :
      ( k3_tarski(k1_tarski(A_20310)) = k1_setfam_1(k1_tarski(A_20310))
      | '#skF_8'(k1_tarski(A_20310),k3_tarski(k1_tarski(A_20310))) = A_20310
      | k1_tarski(A_20310) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_15215,c_262])).

tff(c_20669,plain,(
    ! [A_25408] :
      ( k1_setfam_1(k1_tarski(A_25408)) = A_25408
      | '#skF_8'(k1_tarski(A_25408),A_25408) = A_25408
      | k1_tarski(A_25408) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_15234])).

tff(c_20951,plain,
    ( '#skF_8'(k1_tarski('#skF_9'),'#skF_9') = '#skF_9'
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20669,c_80])).

tff(c_20960,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_20951])).

tff(c_21026,plain,(
    r2_hidden('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20960,c_34])).

tff(c_21083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12897,c_21026])).

tff(c_21085,plain,(
    k1_tarski('#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20951])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21084,plain,(
    '#skF_8'(k1_tarski('#skF_9'),'#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_20951])).

tff(c_76,plain,(
    ! [B_37,A_36] :
      ( ~ r1_tarski(B_37,'#skF_8'(A_36,B_37))
      | r1_tarski(B_37,k1_setfam_1(A_36))
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_21099,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9')))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_21084,c_76])).

tff(c_21146,plain,
    ( r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9')))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_21099])).

tff(c_21147,plain,(
    r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_21085,c_21146])).

tff(c_72,plain,(
    ! [B_34,A_33] :
      ( r1_tarski(k1_setfam_1(B_34),A_33)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_258,plain,(
    ! [B_34,A_33] :
      ( k1_setfam_1(B_34) = A_33
      | ~ r1_tarski(A_33,k1_setfam_1(B_34))
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_72,c_245])).

tff(c_21159,plain,
    ( k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9'
    | ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_21147,c_258])).

tff(c_21216,plain,(
    k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_21159])).

tff(c_21218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_21216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:48:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.63/3.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.63/3.09  
% 9.63/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.63/3.09  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_8 > #skF_9 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 9.63/3.09  
% 9.63/3.09  %Foreground sorts:
% 9.63/3.09  
% 9.63/3.09  
% 9.63/3.09  %Background operators:
% 9.63/3.09  
% 9.63/3.09  
% 9.63/3.09  %Foreground operators:
% 9.63/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.63/3.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.63/3.09  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.63/3.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.63/3.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.63/3.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.63/3.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.63/3.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.63/3.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.63/3.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.63/3.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.63/3.09  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 9.63/3.09  tff('#skF_9', type, '#skF_9': $i).
% 9.63/3.09  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.63/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.63/3.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.63/3.09  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.63/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.63/3.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.63/3.09  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.63/3.09  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.63/3.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.63/3.09  
% 9.63/3.11  tff(f_94, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 9.63/3.11  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.63/3.11  tff(f_64, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 9.63/3.11  tff(f_82, axiom, (![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_setfam_1)).
% 9.63/3.11  tff(f_78, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 9.63/3.11  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.63/3.11  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.63/3.11  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.63/3.11  tff(f_72, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 9.63/3.11  tff(f_91, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 9.63/3.11  tff(f_74, axiom, (![A]: r1_tarski(k1_setfam_1(A), k3_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_setfam_1)).
% 9.63/3.11  tff(c_80, plain, (k1_setfam_1(k1_tarski('#skF_9'))!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.63/3.11  tff(c_34, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.63/3.11  tff(c_46, plain, (![D_24, A_19]: (r2_hidden(D_24, k2_tarski(A_19, D_24)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.63/3.11  tff(c_48, plain, (![D_24, B_20]: (r2_hidden(D_24, k2_tarski(D_24, B_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.63/3.11  tff(c_123, plain, (![A_51]: (k1_setfam_1(A_51)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_51))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.63/3.11  tff(c_137, plain, (![B_20]: (k1_setfam_1(k2_tarski(k1_xboole_0, B_20))=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_123])).
% 9.63/3.11  tff(c_210, plain, (![B_58, A_59]: (r1_tarski(k1_setfam_1(B_58), A_59) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.63/3.11  tff(c_279, plain, (![A_73, B_74]: (r1_tarski(k1_xboole_0, A_73) | ~r2_hidden(A_73, k2_tarski(k1_xboole_0, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_210])).
% 9.63/3.11  tff(c_297, plain, (![D_24]: (r1_tarski(k1_xboole_0, D_24))), inference(resolution, [status(thm)], [c_46, c_279])).
% 9.63/3.11  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.63/3.11  tff(c_8899, plain, (![A_3742, B_3743, C_3744]: (~r2_hidden('#skF_2'(A_3742, B_3743, C_3744), C_3744) | r2_hidden('#skF_3'(A_3742, B_3743, C_3744), C_3744) | k4_xboole_0(A_3742, B_3743)=C_3744)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.63/3.11  tff(c_8963, plain, (![A_3749, B_3750]: (r2_hidden('#skF_3'(A_3749, B_3750, A_3749), A_3749) | k4_xboole_0(A_3749, B_3750)=A_3749)), inference(resolution, [status(thm)], [c_24, c_8899])).
% 9.63/3.11  tff(c_227, plain, (![A_61, B_62]: (r2_hidden('#skF_1'(A_61, B_62), A_61) | r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.63/3.11  tff(c_32, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.63/3.11  tff(c_429, plain, (![A_97, B_98]: ('#skF_1'(k1_tarski(A_97), B_98)=A_97 | r1_tarski(k1_tarski(A_97), B_98))), inference(resolution, [status(thm)], [c_227, c_32])).
% 9.63/3.11  tff(c_323, plain, (![D_78]: (r1_tarski(k1_xboole_0, D_78))), inference(resolution, [status(thm)], [c_46, c_279])).
% 9.63/3.11  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.63/3.11  tff(c_326, plain, (![D_78]: (k1_xboole_0=D_78 | ~r1_tarski(D_78, k1_xboole_0))), inference(resolution, [status(thm)], [c_323, c_26])).
% 9.63/3.11  tff(c_463, plain, (![A_101]: (k1_tarski(A_101)=k1_xboole_0 | '#skF_1'(k1_tarski(A_101), k1_xboole_0)=A_101)), inference(resolution, [status(thm)], [c_429, c_326])).
% 9.63/3.11  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.63/3.11  tff(c_551, plain, (![A_107]: (~r2_hidden(A_107, k1_xboole_0) | r1_tarski(k1_tarski(A_107), k1_xboole_0) | k1_tarski(A_107)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_463, c_4])).
% 9.63/3.11  tff(c_561, plain, (![A_107]: (~r2_hidden(A_107, k1_xboole_0) | k1_tarski(A_107)=k1_xboole_0)), inference(resolution, [status(thm)], [c_551, c_326])).
% 9.63/3.11  tff(c_9029, plain, (![B_3753]: (k1_tarski('#skF_3'(k1_xboole_0, B_3753, k1_xboole_0))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, B_3753)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8963, c_561])).
% 9.63/3.11  tff(c_361, plain, (![C_83, B_84, A_85]: (r2_hidden(C_83, B_84) | ~r2_hidden(C_83, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.63/3.11  tff(c_373, plain, (![C_18, B_84]: (r2_hidden(C_18, B_84) | ~r1_tarski(k1_tarski(C_18), B_84))), inference(resolution, [status(thm)], [c_34, c_361])).
% 9.63/3.11  tff(c_9055, plain, (![B_3753, B_84]: (r2_hidden('#skF_3'(k1_xboole_0, B_3753, k1_xboole_0), B_84) | ~r1_tarski(k1_xboole_0, B_84) | k4_xboole_0(k1_xboole_0, B_3753)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9029, c_373])).
% 9.63/3.11  tff(c_9076, plain, (![B_3753, B_84]: (r2_hidden('#skF_3'(k1_xboole_0, B_3753, k1_xboole_0), B_84) | k4_xboole_0(k1_xboole_0, B_3753)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_297, c_9055])).
% 9.63/3.11  tff(c_9164, plain, (![B_3759, B_3760]: (r2_hidden('#skF_3'(k1_xboole_0, B_3759, k1_xboole_0), B_3760) | k4_xboole_0(k1_xboole_0, B_3759)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_297, c_9055])).
% 9.63/3.11  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.63/3.11  tff(c_12501, plain, (![B_14117, B_14118]: (~r2_hidden('#skF_3'(k1_xboole_0, B_14117, k1_xboole_0), B_14118) | k4_xboole_0(k1_xboole_0, B_14117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9164, c_10])).
% 9.63/3.11  tff(c_12630, plain, (![B_14391]: (k4_xboole_0(k1_xboole_0, B_14391)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9076, c_12501])).
% 9.63/3.11  tff(c_12854, plain, (![D_14806, B_14807]: (~r2_hidden(D_14806, B_14807) | ~r2_hidden(D_14806, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12630, c_10])).
% 9.63/3.11  tff(c_12897, plain, (![D_24]: (~r2_hidden(D_24, k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_12854])).
% 9.63/3.11  tff(c_68, plain, (![A_31]: (k3_tarski(k1_tarski(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.63/3.11  tff(c_565, plain, (![A_108, B_109]: (r2_hidden('#skF_8'(A_108, B_109), A_108) | r1_tarski(B_109, k1_setfam_1(A_108)) | k1_xboole_0=A_108)), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.63/3.11  tff(c_15215, plain, (![A_20310, B_20311]: ('#skF_8'(k1_tarski(A_20310), B_20311)=A_20310 | r1_tarski(B_20311, k1_setfam_1(k1_tarski(A_20310))) | k1_tarski(A_20310)=k1_xboole_0)), inference(resolution, [status(thm)], [c_565, c_32])).
% 9.63/3.11  tff(c_70, plain, (![A_32]: (r1_tarski(k1_setfam_1(A_32), k3_tarski(A_32)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.63/3.11  tff(c_245, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.63/3.11  tff(c_262, plain, (![A_32]: (k3_tarski(A_32)=k1_setfam_1(A_32) | ~r1_tarski(k3_tarski(A_32), k1_setfam_1(A_32)))), inference(resolution, [status(thm)], [c_70, c_245])).
% 9.63/3.11  tff(c_15234, plain, (![A_20310]: (k3_tarski(k1_tarski(A_20310))=k1_setfam_1(k1_tarski(A_20310)) | '#skF_8'(k1_tarski(A_20310), k3_tarski(k1_tarski(A_20310)))=A_20310 | k1_tarski(A_20310)=k1_xboole_0)), inference(resolution, [status(thm)], [c_15215, c_262])).
% 9.63/3.11  tff(c_20669, plain, (![A_25408]: (k1_setfam_1(k1_tarski(A_25408))=A_25408 | '#skF_8'(k1_tarski(A_25408), A_25408)=A_25408 | k1_tarski(A_25408)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_15234])).
% 9.63/3.11  tff(c_20951, plain, ('#skF_8'(k1_tarski('#skF_9'), '#skF_9')='#skF_9' | k1_tarski('#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20669, c_80])).
% 9.63/3.11  tff(c_20960, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_20951])).
% 9.63/3.11  tff(c_21026, plain, (r2_hidden('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20960, c_34])).
% 9.63/3.11  tff(c_21083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12897, c_21026])).
% 9.63/3.11  tff(c_21085, plain, (k1_tarski('#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_20951])).
% 9.63/3.11  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.63/3.11  tff(c_21084, plain, ('#skF_8'(k1_tarski('#skF_9'), '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_20951])).
% 9.63/3.11  tff(c_76, plain, (![B_37, A_36]: (~r1_tarski(B_37, '#skF_8'(A_36, B_37)) | r1_tarski(B_37, k1_setfam_1(A_36)) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.63/3.11  tff(c_21099, plain, (~r1_tarski('#skF_9', '#skF_9') | r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9'))) | k1_tarski('#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_21084, c_76])).
% 9.63/3.11  tff(c_21146, plain, (r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9'))) | k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_21099])).
% 9.63/3.11  tff(c_21147, plain, (r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_21085, c_21146])).
% 9.63/3.11  tff(c_72, plain, (![B_34, A_33]: (r1_tarski(k1_setfam_1(B_34), A_33) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.63/3.11  tff(c_258, plain, (![B_34, A_33]: (k1_setfam_1(B_34)=A_33 | ~r1_tarski(A_33, k1_setfam_1(B_34)) | ~r2_hidden(A_33, B_34))), inference(resolution, [status(thm)], [c_72, c_245])).
% 9.63/3.11  tff(c_21159, plain, (k1_setfam_1(k1_tarski('#skF_9'))='#skF_9' | ~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_21147, c_258])).
% 9.63/3.11  tff(c_21216, plain, (k1_setfam_1(k1_tarski('#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_21159])).
% 9.63/3.11  tff(c_21218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_21216])).
% 9.63/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.63/3.11  
% 9.63/3.11  Inference rules
% 9.63/3.11  ----------------------
% 9.63/3.11  #Ref     : 0
% 9.63/3.11  #Sup     : 3601
% 9.63/3.11  #Fact    : 10
% 9.63/3.11  #Define  : 0
% 9.63/3.11  #Split   : 4
% 9.63/3.11  #Chain   : 0
% 9.63/3.11  #Close   : 0
% 9.63/3.11  
% 9.63/3.11  Ordering : KBO
% 9.63/3.11  
% 9.63/3.11  Simplification rules
% 9.63/3.11  ----------------------
% 9.63/3.11  #Subsume      : 1097
% 9.63/3.11  #Demod        : 1023
% 9.63/3.11  #Tautology    : 733
% 9.63/3.11  #SimpNegUnit  : 29
% 9.63/3.11  #BackRed      : 4
% 9.63/3.11  
% 9.63/3.11  #Partial instantiations: 12750
% 9.63/3.11  #Strategies tried      : 1
% 9.63/3.11  
% 9.63/3.11  Timing (in seconds)
% 9.63/3.11  ----------------------
% 9.63/3.11  Preprocessing        : 0.33
% 9.63/3.11  Parsing              : 0.17
% 9.63/3.11  CNF conversion       : 0.03
% 9.63/3.11  Main loop            : 2.00
% 9.63/3.11  Inferencing          : 0.81
% 9.63/3.11  Reduction            : 0.52
% 9.63/3.11  Demodulation         : 0.36
% 9.63/3.11  BG Simplification    : 0.08
% 9.63/3.11  Subsumption          : 0.43
% 9.63/3.11  Abstraction          : 0.10
% 9.63/3.11  MUC search           : 0.00
% 9.63/3.11  Cooper               : 0.00
% 9.63/3.11  Total                : 2.37
% 9.63/3.11  Index Insertion      : 0.00
% 9.63/3.11  Index Deletion       : 0.00
% 9.63/3.11  Index Matching       : 0.00
% 9.63/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
