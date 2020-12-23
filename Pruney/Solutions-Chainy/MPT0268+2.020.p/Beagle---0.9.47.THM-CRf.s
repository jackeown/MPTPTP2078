%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:36 EST 2020

% Result     : Theorem 7.96s
% Output     : CNFRefutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 189 expanded)
%              Number of leaves         :   39 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          :  106 ( 245 expanded)
%              Number of equality atoms :   48 ( 113 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_86,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_76,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_100,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_22,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_208,plain,(
    ! [A_88,B_89] : k4_xboole_0(A_88,k4_xboole_0(A_88,B_89)) = k3_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    ! [A_22,B_23] : r1_xboole_0(k4_xboole_0(A_22,B_23),B_23) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_232,plain,(
    ! [A_90,B_91] : r1_xboole_0(k3_xboole_0(A_90,B_91),k4_xboole_0(A_90,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_34])).

tff(c_244,plain,(
    ! [A_9] : r1_xboole_0(A_9,k4_xboole_0(A_9,A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_232])).

tff(c_28,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_4'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_245,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | ~ r2_hidden(C_94,k3_xboole_0(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_267,plain,(
    ! [A_98,B_99] :
      ( ~ r1_xboole_0(A_98,B_99)
      | k3_xboole_0(A_98,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_245])).

tff(c_326,plain,(
    ! [A_103] : k3_xboole_0(A_103,k4_xboole_0(A_103,A_103)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_244,c_267])).

tff(c_223,plain,(
    ! [A_88,B_89] : r1_xboole_0(k3_xboole_0(A_88,B_89),k4_xboole_0(A_88,B_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_34])).

tff(c_334,plain,(
    ! [A_103] : r1_xboole_0(k1_xboole_0,k4_xboole_0(A_103,k4_xboole_0(A_103,A_103))) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_223])).

tff(c_345,plain,(
    ! [A_104] : r1_xboole_0(k1_xboole_0,A_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_32,c_334])).

tff(c_259,plain,(
    ! [A_92,B_93] :
      ( ~ r1_xboole_0(A_92,B_93)
      | k3_xboole_0(A_92,B_93) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_245])).

tff(c_354,plain,(
    ! [A_105] : k3_xboole_0(k1_xboole_0,A_105) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_345,c_259])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_414,plain,(
    ! [A_109] : k3_xboole_0(A_109,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_2])).

tff(c_30,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_431,plain,(
    ! [A_109] : k5_xboole_0(A_109,k1_xboole_0) = k4_xboole_0(A_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_30])).

tff(c_284,plain,(
    ! [A_100,B_101] : k3_xboole_0(k4_xboole_0(A_100,B_101),B_101) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_267])).

tff(c_522,plain,(
    ! [B_113,A_114] : k3_xboole_0(B_113,k4_xboole_0(A_114,B_113)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_284])).

tff(c_539,plain,(
    ! [B_113,A_114] : k4_xboole_0(B_113,k4_xboole_0(A_114,B_113)) = k5_xboole_0(B_113,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_30])).

tff(c_2640,plain,(
    ! [B_240,A_241] : k4_xboole_0(B_240,k4_xboole_0(A_241,B_240)) = k4_xboole_0(B_240,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_539])).

tff(c_2693,plain,(
    ! [A_241] : k4_xboole_0(A_241,k1_xboole_0) = k3_xboole_0(A_241,A_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_2640,c_32])).

tff(c_2734,plain,(
    ! [A_241] : k4_xboole_0(A_241,k1_xboole_0) = A_241 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2693])).

tff(c_72,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1261,plain,(
    ! [A_176,B_177] :
      ( k3_xboole_0(k1_tarski(A_176),B_177) = k1_xboole_0
      | r2_hidden(A_176,B_177) ) ),
    inference(resolution,[status(thm)],[c_72,c_267])).

tff(c_181,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_193,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_181])).

tff(c_1273,plain,(
    ! [B_177,A_176] :
      ( k4_xboole_0(B_177,k1_tarski(A_176)) = k5_xboole_0(B_177,k1_xboole_0)
      | r2_hidden(A_176,B_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1261,c_193])).

tff(c_1337,plain,(
    ! [B_177,A_176] :
      ( k4_xboole_0(B_177,k1_tarski(A_176)) = k4_xboole_0(B_177,k1_xboole_0)
      | r2_hidden(A_176,B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_1273])).

tff(c_12439,plain,(
    ! [B_413,A_414] :
      ( k4_xboole_0(B_413,k1_tarski(A_414)) = B_413
      | r2_hidden(A_414,B_413) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2734,c_1337])).

tff(c_74,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_180,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_12574,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12439,c_180])).

tff(c_12626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_12574])).

tff(c_12627,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_60,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_139,plain,(
    ! [A_72,B_73] : k1_enumset1(A_72,A_72,B_73) = k2_tarski(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    ! [E_30,A_24,C_26] : r2_hidden(E_30,k1_enumset1(A_24,E_30,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_157,plain,(
    ! [A_74,B_75] : r2_hidden(A_74,k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_40])).

tff(c_160,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_157])).

tff(c_12628,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12697,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12628,c_78])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13108,plain,(
    ! [D_435] :
      ( ~ r2_hidden(D_435,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_435,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12697,c_6])).

tff(c_13112,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_160,c_13108])).

tff(c_13120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12627,c_13112])).

tff(c_13121,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_13160,plain,(
    ! [A_448,B_449] : k1_enumset1(A_448,A_448,B_449) = k2_tarski(A_448,B_449) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    ! [E_30,A_24,B_25] : r2_hidden(E_30,k1_enumset1(A_24,B_25,E_30)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_13178,plain,(
    ! [B_450,A_451] : r2_hidden(B_450,k2_tarski(A_451,B_450)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13160,c_38])).

tff(c_13181,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_13178])).

tff(c_13122,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_13250,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13122,c_80])).

tff(c_13321,plain,(
    ! [D_470,B_471,A_472] :
      ( ~ r2_hidden(D_470,B_471)
      | ~ r2_hidden(D_470,k4_xboole_0(A_472,B_471)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13334,plain,(
    ! [D_473] :
      ( ~ r2_hidden(D_473,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_473,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13250,c_13321])).

tff(c_13338,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_13181,c_13334])).

tff(c_13346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13121,c_13338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.96/2.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/2.82  
% 7.96/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/2.83  %$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5
% 7.96/2.83  
% 7.96/2.83  %Foreground sorts:
% 7.96/2.83  
% 7.96/2.83  
% 7.96/2.83  %Background operators:
% 7.96/2.83  
% 7.96/2.83  
% 7.96/2.83  %Foreground operators:
% 7.96/2.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.96/2.83  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.96/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.96/2.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.96/2.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.96/2.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.96/2.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.96/2.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.96/2.83  tff('#skF_7', type, '#skF_7': $i).
% 7.96/2.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.96/2.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.96/2.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.96/2.83  tff('#skF_10', type, '#skF_10': $i).
% 7.96/2.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.96/2.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.96/2.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.96/2.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.96/2.83  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.96/2.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.96/2.83  tff('#skF_9', type, '#skF_9': $i).
% 7.96/2.83  tff('#skF_8', type, '#skF_8': $i).
% 7.96/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.96/2.83  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 7.96/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.96/2.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.96/2.83  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.96/2.83  
% 7.96/2.84  tff(f_105, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.96/2.84  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.96/2.84  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.96/2.84  tff(f_67, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.96/2.84  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.96/2.84  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.96/2.84  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.96/2.84  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.96/2.84  tff(f_99, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.96/2.84  tff(f_84, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.96/2.84  tff(f_86, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.96/2.84  tff(f_82, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.96/2.84  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.96/2.84  tff(c_76, plain, (~r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.96/2.84  tff(c_100, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_76])).
% 7.96/2.84  tff(c_22, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.96/2.84  tff(c_32, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.96/2.84  tff(c_208, plain, (![A_88, B_89]: (k4_xboole_0(A_88, k4_xboole_0(A_88, B_89))=k3_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.96/2.84  tff(c_34, plain, (![A_22, B_23]: (r1_xboole_0(k4_xboole_0(A_22, B_23), B_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.96/2.84  tff(c_232, plain, (![A_90, B_91]: (r1_xboole_0(k3_xboole_0(A_90, B_91), k4_xboole_0(A_90, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_208, c_34])).
% 7.96/2.84  tff(c_244, plain, (![A_9]: (r1_xboole_0(A_9, k4_xboole_0(A_9, A_9)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_232])).
% 7.96/2.84  tff(c_28, plain, (![A_16]: (r2_hidden('#skF_4'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.96/2.84  tff(c_245, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | ~r2_hidden(C_94, k3_xboole_0(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.96/2.84  tff(c_267, plain, (![A_98, B_99]: (~r1_xboole_0(A_98, B_99) | k3_xboole_0(A_98, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_245])).
% 7.96/2.84  tff(c_326, plain, (![A_103]: (k3_xboole_0(A_103, k4_xboole_0(A_103, A_103))=k1_xboole_0)), inference(resolution, [status(thm)], [c_244, c_267])).
% 7.96/2.84  tff(c_223, plain, (![A_88, B_89]: (r1_xboole_0(k3_xboole_0(A_88, B_89), k4_xboole_0(A_88, B_89)))), inference(superposition, [status(thm), theory('equality')], [c_208, c_34])).
% 7.96/2.84  tff(c_334, plain, (![A_103]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(A_103, k4_xboole_0(A_103, A_103))))), inference(superposition, [status(thm), theory('equality')], [c_326, c_223])).
% 7.96/2.84  tff(c_345, plain, (![A_104]: (r1_xboole_0(k1_xboole_0, A_104))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_32, c_334])).
% 7.96/2.84  tff(c_259, plain, (![A_92, B_93]: (~r1_xboole_0(A_92, B_93) | k3_xboole_0(A_92, B_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_245])).
% 7.96/2.84  tff(c_354, plain, (![A_105]: (k3_xboole_0(k1_xboole_0, A_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_345, c_259])).
% 7.96/2.84  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.96/2.84  tff(c_414, plain, (![A_109]: (k3_xboole_0(A_109, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_354, c_2])).
% 7.96/2.84  tff(c_30, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.96/2.84  tff(c_431, plain, (![A_109]: (k5_xboole_0(A_109, k1_xboole_0)=k4_xboole_0(A_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_414, c_30])).
% 7.96/2.84  tff(c_284, plain, (![A_100, B_101]: (k3_xboole_0(k4_xboole_0(A_100, B_101), B_101)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_267])).
% 7.96/2.84  tff(c_522, plain, (![B_113, A_114]: (k3_xboole_0(B_113, k4_xboole_0(A_114, B_113))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_284])).
% 7.96/2.84  tff(c_539, plain, (![B_113, A_114]: (k4_xboole_0(B_113, k4_xboole_0(A_114, B_113))=k5_xboole_0(B_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_522, c_30])).
% 7.96/2.84  tff(c_2640, plain, (![B_240, A_241]: (k4_xboole_0(B_240, k4_xboole_0(A_241, B_240))=k4_xboole_0(B_240, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_431, c_539])).
% 7.96/2.84  tff(c_2693, plain, (![A_241]: (k4_xboole_0(A_241, k1_xboole_0)=k3_xboole_0(A_241, A_241))), inference(superposition, [status(thm), theory('equality')], [c_2640, c_32])).
% 7.96/2.84  tff(c_2734, plain, (![A_241]: (k4_xboole_0(A_241, k1_xboole_0)=A_241)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2693])).
% 7.96/2.84  tff(c_72, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.96/2.84  tff(c_1261, plain, (![A_176, B_177]: (k3_xboole_0(k1_tarski(A_176), B_177)=k1_xboole_0 | r2_hidden(A_176, B_177))), inference(resolution, [status(thm)], [c_72, c_267])).
% 7.96/2.84  tff(c_181, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.96/2.84  tff(c_193, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_181])).
% 7.96/2.84  tff(c_1273, plain, (![B_177, A_176]: (k4_xboole_0(B_177, k1_tarski(A_176))=k5_xboole_0(B_177, k1_xboole_0) | r2_hidden(A_176, B_177))), inference(superposition, [status(thm), theory('equality')], [c_1261, c_193])).
% 7.96/2.84  tff(c_1337, plain, (![B_177, A_176]: (k4_xboole_0(B_177, k1_tarski(A_176))=k4_xboole_0(B_177, k1_xboole_0) | r2_hidden(A_176, B_177))), inference(demodulation, [status(thm), theory('equality')], [c_431, c_1273])).
% 7.96/2.84  tff(c_12439, plain, (![B_413, A_414]: (k4_xboole_0(B_413, k1_tarski(A_414))=B_413 | r2_hidden(A_414, B_413))), inference(demodulation, [status(thm), theory('equality')], [c_2734, c_1337])).
% 7.96/2.84  tff(c_74, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.96/2.84  tff(c_180, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_74])).
% 7.96/2.84  tff(c_12574, plain, (r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12439, c_180])).
% 7.96/2.84  tff(c_12626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_12574])).
% 7.96/2.84  tff(c_12627, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_74])).
% 7.96/2.84  tff(c_60, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.96/2.84  tff(c_139, plain, (![A_72, B_73]: (k1_enumset1(A_72, A_72, B_73)=k2_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.96/2.84  tff(c_40, plain, (![E_30, A_24, C_26]: (r2_hidden(E_30, k1_enumset1(A_24, E_30, C_26)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.96/2.84  tff(c_157, plain, (![A_74, B_75]: (r2_hidden(A_74, k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_40])).
% 7.96/2.84  tff(c_160, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_157])).
% 7.96/2.84  tff(c_12628, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 7.96/2.84  tff(c_78, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.96/2.84  tff(c_12697, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_12628, c_78])).
% 7.96/2.84  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.96/2.84  tff(c_13108, plain, (![D_435]: (~r2_hidden(D_435, k1_tarski('#skF_10')) | ~r2_hidden(D_435, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_12697, c_6])).
% 7.96/2.84  tff(c_13112, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_160, c_13108])).
% 7.96/2.84  tff(c_13120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12627, c_13112])).
% 7.96/2.84  tff(c_13121, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_76])).
% 7.96/2.84  tff(c_13160, plain, (![A_448, B_449]: (k1_enumset1(A_448, A_448, B_449)=k2_tarski(A_448, B_449))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.96/2.84  tff(c_38, plain, (![E_30, A_24, B_25]: (r2_hidden(E_30, k1_enumset1(A_24, B_25, E_30)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.96/2.84  tff(c_13178, plain, (![B_450, A_451]: (r2_hidden(B_450, k2_tarski(A_451, B_450)))), inference(superposition, [status(thm), theory('equality')], [c_13160, c_38])).
% 7.96/2.84  tff(c_13181, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_13178])).
% 7.96/2.84  tff(c_13122, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_76])).
% 7.96/2.84  tff(c_80, plain, (~r2_hidden('#skF_8', '#skF_7') | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.96/2.84  tff(c_13250, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_13122, c_80])).
% 7.96/2.84  tff(c_13321, plain, (![D_470, B_471, A_472]: (~r2_hidden(D_470, B_471) | ~r2_hidden(D_470, k4_xboole_0(A_472, B_471)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.96/2.84  tff(c_13334, plain, (![D_473]: (~r2_hidden(D_473, k1_tarski('#skF_10')) | ~r2_hidden(D_473, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_13250, c_13321])).
% 7.96/2.84  tff(c_13338, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_13181, c_13334])).
% 7.96/2.84  tff(c_13346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13121, c_13338])).
% 7.96/2.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/2.84  
% 7.96/2.84  Inference rules
% 7.96/2.84  ----------------------
% 7.96/2.84  #Ref     : 0
% 7.96/2.84  #Sup     : 3199
% 7.96/2.84  #Fact    : 6
% 7.96/2.84  #Define  : 0
% 7.96/2.84  #Split   : 2
% 7.96/2.84  #Chain   : 0
% 7.96/2.84  #Close   : 0
% 7.96/2.84  
% 7.96/2.84  Ordering : KBO
% 7.96/2.84  
% 7.96/2.84  Simplification rules
% 7.96/2.84  ----------------------
% 7.96/2.84  #Subsume      : 608
% 7.96/2.84  #Demod        : 2342
% 7.96/2.84  #Tautology    : 1707
% 7.96/2.84  #SimpNegUnit  : 79
% 7.96/2.84  #BackRed      : 5
% 7.96/2.84  
% 7.96/2.84  #Partial instantiations: 0
% 7.96/2.84  #Strategies tried      : 1
% 7.96/2.84  
% 7.96/2.84  Timing (in seconds)
% 7.96/2.84  ----------------------
% 7.96/2.85  Preprocessing        : 0.32
% 7.96/2.85  Parsing              : 0.16
% 7.96/2.85  CNF conversion       : 0.03
% 7.96/2.85  Main loop            : 1.74
% 7.96/2.85  Inferencing          : 0.51
% 7.96/2.85  Reduction            : 0.71
% 7.96/2.85  Demodulation         : 0.57
% 7.96/2.85  BG Simplification    : 0.06
% 7.96/2.85  Subsumption          : 0.35
% 7.96/2.85  Abstraction          : 0.08
% 7.96/2.85  MUC search           : 0.00
% 7.96/2.85  Cooper               : 0.00
% 7.96/2.85  Total                : 2.10
% 7.96/2.85  Index Insertion      : 0.00
% 7.96/2.85  Index Deletion       : 0.00
% 7.96/2.85  Index Matching       : 0.00
% 7.96/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
