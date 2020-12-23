%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:56 EST 2020

% Result     : Theorem 8.09s
% Output     : CNFRefutation 8.09s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 144 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  129 ( 232 expanded)
%              Number of equality atoms :   43 (  72 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5

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

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_94,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_86,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_151,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_44,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_4'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_180,plain,(
    ! [D_67,A_68,B_69] :
      ( r2_hidden(D_67,A_68)
      | ~ r2_hidden(D_67,k3_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_191,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_68,B_69)),A_68)
      | k3_xboole_0(A_68,B_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_180])).

tff(c_46,plain,(
    ! [A_22,B_23] : r1_xboole_0(k4_xboole_0(A_22,B_23),B_23) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_289,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r1_xboole_0(A_87,B_88)
      | ~ r2_hidden(C_89,B_88)
      | ~ r2_hidden(C_89,A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_314,plain,(
    ! [C_92,B_93,A_94] :
      ( ~ r2_hidden(C_92,B_93)
      | ~ r2_hidden(C_92,k4_xboole_0(A_94,B_93)) ) ),
    inference(resolution,[status(thm)],[c_46,c_289])).

tff(c_496,plain,(
    ! [A_115,B_116] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_115,B_116)),B_116)
      | k4_xboole_0(A_115,B_116) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_314])).

tff(c_506,plain,(
    ! [A_21] :
      ( ~ r2_hidden('#skF_4'(A_21),k1_xboole_0)
      | k4_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_496])).

tff(c_509,plain,(
    ! [A_117] :
      ( ~ r2_hidden('#skF_4'(A_117),k1_xboole_0)
      | k1_xboole_0 = A_117 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_506])).

tff(c_526,plain,(
    ! [B_118] : k3_xboole_0(k1_xboole_0,B_118) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_191,c_509])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_245,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_257,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_245])).

tff(c_537,plain,(
    ! [B_118] : k5_xboole_0(B_118,k1_xboole_0) = k4_xboole_0(B_118,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_257])).

tff(c_566,plain,(
    ! [B_118] : k5_xboole_0(B_118,k1_xboole_0) = B_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_537])).

tff(c_82,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,k1_tarski(B_42)) = A_41
      | r2_hidden(B_42,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_218,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_3'(A_77,B_78),A_77)
      | r1_xboole_0(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_228,plain,(
    ! [A_3,B_4,B_78] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_3,B_4),B_78),A_3)
      | r1_xboole_0(k3_xboole_0(A_3,B_4),B_78) ) ),
    inference(resolution,[status(thm)],[c_218,c_8])).

tff(c_36,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),B_13)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2782,plain,(
    ! [A_247,A_248,B_249] :
      ( ~ r2_hidden('#skF_3'(A_247,k4_xboole_0(A_248,B_249)),B_249)
      | r1_xboole_0(A_247,k4_xboole_0(A_248,B_249)) ) ),
    inference(resolution,[status(thm)],[c_36,c_314])).

tff(c_2874,plain,(
    ! [A_259,B_260,A_261] : r1_xboole_0(k3_xboole_0(A_259,B_260),k4_xboole_0(A_261,A_259)) ),
    inference(resolution,[status(thm)],[c_228,c_2782])).

tff(c_3037,plain,(
    ! [B_271,B_272,A_273] :
      ( r1_xboole_0(k3_xboole_0(k1_tarski(B_271),B_272),A_273)
      | r2_hidden(B_271,A_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2874])).

tff(c_34,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,B_13)
      | ~ r2_hidden(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8272,plain,(
    ! [C_430,A_431,B_432,B_433] :
      ( ~ r2_hidden(C_430,A_431)
      | ~ r2_hidden(C_430,k3_xboole_0(k1_tarski(B_432),B_433))
      | r2_hidden(B_432,A_431) ) ),
    inference(resolution,[status(thm)],[c_3037,c_34])).

tff(c_9061,plain,(
    ! [A_459,B_460,B_461] :
      ( ~ r2_hidden('#skF_4'(A_459),k3_xboole_0(k1_tarski(B_460),B_461))
      | r2_hidden(B_460,A_459)
      | k1_xboole_0 = A_459 ) ),
    inference(resolution,[status(thm)],[c_40,c_8272])).

tff(c_9218,plain,(
    ! [B_464,B_465] :
      ( r2_hidden(B_464,k3_xboole_0(k1_tarski(B_464),B_465))
      | k3_xboole_0(k1_tarski(B_464),B_465) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_9061])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9299,plain,(
    ! [B_466,B_467] :
      ( r2_hidden(B_466,B_467)
      | k3_xboole_0(k1_tarski(B_466),B_467) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9218,c_6])).

tff(c_42,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9431,plain,(
    ! [B_466,B_467] :
      ( k5_xboole_0(k1_tarski(B_466),k1_xboole_0) = k4_xboole_0(k1_tarski(B_466),B_467)
      | r2_hidden(B_466,B_467) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9299,c_42])).

tff(c_10023,plain,(
    ! [B_473,B_474] :
      ( k4_xboole_0(k1_tarski(B_473),B_474) = k1_tarski(B_473)
      | r2_hidden(B_473,B_474) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_9431])).

tff(c_84,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_tarski('#skF_7')
    | r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_260,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_tarski('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_10076,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_10023,c_260])).

tff(c_10116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_10076])).

tff(c_10117,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_72,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_152,plain,(
    ! [A_60,B_61] : k1_enumset1(A_60,A_60,B_61) = k2_tarski(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50,plain,(
    ! [E_30,A_24,B_25] : r2_hidden(E_30,k1_enumset1(A_24,B_25,E_30)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_170,plain,(
    ! [B_62,A_63] : r2_hidden(B_62,k2_tarski(A_63,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_50])).

tff(c_173,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_170])).

tff(c_10118,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_tarski('#skF_7')
    | k4_xboole_0(k1_tarski('#skF_9'),'#skF_10') = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10127,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),'#skF_10') = k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10118,c_88])).

tff(c_10131,plain,(
    r1_xboole_0(k1_tarski('#skF_9'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_10127,c_46])).

tff(c_10172,plain,(
    ! [A_480,B_481,C_482] :
      ( ~ r1_xboole_0(A_480,B_481)
      | ~ r2_hidden(C_482,B_481)
      | ~ r2_hidden(C_482,A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10203,plain,(
    ! [C_485] :
      ( ~ r2_hidden(C_485,'#skF_10')
      | ~ r2_hidden(C_485,k1_tarski('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_10131,c_10172])).

tff(c_10215,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_173,c_10203])).

tff(c_10225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10117,c_10215])).

tff(c_10226,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_10228,plain,(
    ! [A_486,B_487] : k1_enumset1(A_486,A_486,B_487) = k2_tarski(A_486,B_487) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10246,plain,(
    ! [B_488,A_489] : r2_hidden(B_488,k2_tarski(A_489,B_488)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10228,c_50])).

tff(c_10249,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_10246])).

tff(c_10227,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_90,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | k4_xboole_0(k1_tarski('#skF_9'),'#skF_10') = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10285,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),'#skF_10') = k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10227,c_90])).

tff(c_10289,plain,(
    r1_xboole_0(k1_tarski('#skF_9'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_10285,c_46])).

tff(c_10374,plain,(
    ! [A_513,B_514,C_515] :
      ( ~ r1_xboole_0(A_513,B_514)
      | ~ r2_hidden(C_515,B_514)
      | ~ r2_hidden(C_515,A_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10402,plain,(
    ! [C_518] :
      ( ~ r2_hidden(C_518,'#skF_10')
      | ~ r2_hidden(C_518,k1_tarski('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_10289,c_10374])).

tff(c_10414,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_10249,c_10402])).

tff(c_10424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10226,c_10414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:24:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.09/2.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.91  
% 8.09/2.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.91  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5
% 8.09/2.91  
% 8.09/2.91  %Foreground sorts:
% 8.09/2.91  
% 8.09/2.91  
% 8.09/2.91  %Background operators:
% 8.09/2.91  
% 8.09/2.91  
% 8.09/2.91  %Foreground operators:
% 8.09/2.91  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.09/2.91  tff('#skF_4', type, '#skF_4': $i > $i).
% 8.09/2.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.09/2.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.09/2.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.09/2.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.09/2.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.09/2.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.09/2.91  tff('#skF_7', type, '#skF_7': $i).
% 8.09/2.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.09/2.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.09/2.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.09/2.91  tff('#skF_10', type, '#skF_10': $i).
% 8.09/2.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.09/2.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.09/2.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.09/2.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.09/2.91  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 8.09/2.91  tff('#skF_9', type, '#skF_9': $i).
% 8.09/2.91  tff('#skF_8', type, '#skF_8': $i).
% 8.09/2.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.09/2.91  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 8.09/2.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.09/2.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.09/2.91  
% 8.09/2.93  tff(f_109, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 8.09/2.93  tff(f_73, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.09/2.93  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.09/2.93  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.09/2.93  tff(f_75, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 8.09/2.93  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.09/2.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.09/2.93  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.09/2.93  tff(f_103, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 8.09/2.93  tff(f_92, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.09/2.93  tff(f_94, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 8.09/2.93  tff(f_90, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 8.09/2.93  tff(c_86, plain, (~r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.09/2.93  tff(c_151, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_86])).
% 8.09/2.93  tff(c_44, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.09/2.93  tff(c_40, plain, (![A_17]: (r2_hidden('#skF_4'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.09/2.93  tff(c_180, plain, (![D_67, A_68, B_69]: (r2_hidden(D_67, A_68) | ~r2_hidden(D_67, k3_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.09/2.93  tff(c_191, plain, (![A_68, B_69]: (r2_hidden('#skF_4'(k3_xboole_0(A_68, B_69)), A_68) | k3_xboole_0(A_68, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_180])).
% 8.09/2.93  tff(c_46, plain, (![A_22, B_23]: (r1_xboole_0(k4_xboole_0(A_22, B_23), B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.09/2.93  tff(c_289, plain, (![A_87, B_88, C_89]: (~r1_xboole_0(A_87, B_88) | ~r2_hidden(C_89, B_88) | ~r2_hidden(C_89, A_87))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.09/2.93  tff(c_314, plain, (![C_92, B_93, A_94]: (~r2_hidden(C_92, B_93) | ~r2_hidden(C_92, k4_xboole_0(A_94, B_93)))), inference(resolution, [status(thm)], [c_46, c_289])).
% 8.09/2.93  tff(c_496, plain, (![A_115, B_116]: (~r2_hidden('#skF_4'(k4_xboole_0(A_115, B_116)), B_116) | k4_xboole_0(A_115, B_116)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_314])).
% 8.09/2.93  tff(c_506, plain, (![A_21]: (~r2_hidden('#skF_4'(A_21), k1_xboole_0) | k4_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_496])).
% 8.09/2.93  tff(c_509, plain, (![A_117]: (~r2_hidden('#skF_4'(A_117), k1_xboole_0) | k1_xboole_0=A_117)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_506])).
% 8.09/2.93  tff(c_526, plain, (![B_118]: (k3_xboole_0(k1_xboole_0, B_118)=k1_xboole_0)), inference(resolution, [status(thm)], [c_191, c_509])).
% 8.09/2.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.09/2.93  tff(c_245, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.09/2.93  tff(c_257, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_245])).
% 8.09/2.93  tff(c_537, plain, (![B_118]: (k5_xboole_0(B_118, k1_xboole_0)=k4_xboole_0(B_118, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_526, c_257])).
% 8.09/2.93  tff(c_566, plain, (![B_118]: (k5_xboole_0(B_118, k1_xboole_0)=B_118)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_537])).
% 8.09/2.93  tff(c_82, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k1_tarski(B_42))=A_41 | r2_hidden(B_42, A_41))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.09/2.93  tff(c_218, plain, (![A_77, B_78]: (r2_hidden('#skF_3'(A_77, B_78), A_77) | r1_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.09/2.93  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.09/2.93  tff(c_228, plain, (![A_3, B_4, B_78]: (r2_hidden('#skF_3'(k3_xboole_0(A_3, B_4), B_78), A_3) | r1_xboole_0(k3_xboole_0(A_3, B_4), B_78))), inference(resolution, [status(thm)], [c_218, c_8])).
% 8.09/2.93  tff(c_36, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), B_13) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.09/2.93  tff(c_2782, plain, (![A_247, A_248, B_249]: (~r2_hidden('#skF_3'(A_247, k4_xboole_0(A_248, B_249)), B_249) | r1_xboole_0(A_247, k4_xboole_0(A_248, B_249)))), inference(resolution, [status(thm)], [c_36, c_314])).
% 8.09/2.93  tff(c_2874, plain, (![A_259, B_260, A_261]: (r1_xboole_0(k3_xboole_0(A_259, B_260), k4_xboole_0(A_261, A_259)))), inference(resolution, [status(thm)], [c_228, c_2782])).
% 8.09/2.93  tff(c_3037, plain, (![B_271, B_272, A_273]: (r1_xboole_0(k3_xboole_0(k1_tarski(B_271), B_272), A_273) | r2_hidden(B_271, A_273))), inference(superposition, [status(thm), theory('equality')], [c_82, c_2874])).
% 8.09/2.93  tff(c_34, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, B_13) | ~r2_hidden(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.09/2.93  tff(c_8272, plain, (![C_430, A_431, B_432, B_433]: (~r2_hidden(C_430, A_431) | ~r2_hidden(C_430, k3_xboole_0(k1_tarski(B_432), B_433)) | r2_hidden(B_432, A_431))), inference(resolution, [status(thm)], [c_3037, c_34])).
% 8.09/2.93  tff(c_9061, plain, (![A_459, B_460, B_461]: (~r2_hidden('#skF_4'(A_459), k3_xboole_0(k1_tarski(B_460), B_461)) | r2_hidden(B_460, A_459) | k1_xboole_0=A_459)), inference(resolution, [status(thm)], [c_40, c_8272])).
% 8.09/2.93  tff(c_9218, plain, (![B_464, B_465]: (r2_hidden(B_464, k3_xboole_0(k1_tarski(B_464), B_465)) | k3_xboole_0(k1_tarski(B_464), B_465)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_9061])).
% 8.09/2.93  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.09/2.93  tff(c_9299, plain, (![B_466, B_467]: (r2_hidden(B_466, B_467) | k3_xboole_0(k1_tarski(B_466), B_467)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9218, c_6])).
% 8.09/2.93  tff(c_42, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.09/2.93  tff(c_9431, plain, (![B_466, B_467]: (k5_xboole_0(k1_tarski(B_466), k1_xboole_0)=k4_xboole_0(k1_tarski(B_466), B_467) | r2_hidden(B_466, B_467))), inference(superposition, [status(thm), theory('equality')], [c_9299, c_42])).
% 8.09/2.93  tff(c_10023, plain, (![B_473, B_474]: (k4_xboole_0(k1_tarski(B_473), B_474)=k1_tarski(B_473) | r2_hidden(B_473, B_474))), inference(demodulation, [status(thm), theory('equality')], [c_566, c_9431])).
% 8.09/2.93  tff(c_84, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_tarski('#skF_7') | r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.09/2.93  tff(c_260, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_tarski('#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 8.09/2.93  tff(c_10076, plain, (r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_10023, c_260])).
% 8.09/2.93  tff(c_10116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_10076])).
% 8.09/2.93  tff(c_10117, plain, (r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_84])).
% 8.09/2.93  tff(c_72, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.09/2.93  tff(c_152, plain, (![A_60, B_61]: (k1_enumset1(A_60, A_60, B_61)=k2_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.09/2.93  tff(c_50, plain, (![E_30, A_24, B_25]: (r2_hidden(E_30, k1_enumset1(A_24, B_25, E_30)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.09/2.93  tff(c_170, plain, (![B_62, A_63]: (r2_hidden(B_62, k2_tarski(A_63, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_50])).
% 8.09/2.93  tff(c_173, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_170])).
% 8.09/2.93  tff(c_10118, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 8.09/2.93  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_tarski('#skF_7') | k4_xboole_0(k1_tarski('#skF_9'), '#skF_10')=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.09/2.93  tff(c_10127, plain, (k4_xboole_0(k1_tarski('#skF_9'), '#skF_10')=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_10118, c_88])).
% 8.09/2.93  tff(c_10131, plain, (r1_xboole_0(k1_tarski('#skF_9'), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_10127, c_46])).
% 8.09/2.93  tff(c_10172, plain, (![A_480, B_481, C_482]: (~r1_xboole_0(A_480, B_481) | ~r2_hidden(C_482, B_481) | ~r2_hidden(C_482, A_480))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.09/2.93  tff(c_10203, plain, (![C_485]: (~r2_hidden(C_485, '#skF_10') | ~r2_hidden(C_485, k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_10131, c_10172])).
% 8.09/2.93  tff(c_10215, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_173, c_10203])).
% 8.09/2.93  tff(c_10225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10117, c_10215])).
% 8.09/2.93  tff(c_10226, plain, (r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_86])).
% 8.09/2.93  tff(c_10228, plain, (![A_486, B_487]: (k1_enumset1(A_486, A_486, B_487)=k2_tarski(A_486, B_487))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.09/2.93  tff(c_10246, plain, (![B_488, A_489]: (r2_hidden(B_488, k2_tarski(A_489, B_488)))), inference(superposition, [status(thm), theory('equality')], [c_10228, c_50])).
% 8.09/2.93  tff(c_10249, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_10246])).
% 8.09/2.93  tff(c_10227, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_86])).
% 8.09/2.93  tff(c_90, plain, (~r2_hidden('#skF_7', '#skF_8') | k4_xboole_0(k1_tarski('#skF_9'), '#skF_10')=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.09/2.93  tff(c_10285, plain, (k4_xboole_0(k1_tarski('#skF_9'), '#skF_10')=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_10227, c_90])).
% 8.09/2.93  tff(c_10289, plain, (r1_xboole_0(k1_tarski('#skF_9'), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_10285, c_46])).
% 8.09/2.93  tff(c_10374, plain, (![A_513, B_514, C_515]: (~r1_xboole_0(A_513, B_514) | ~r2_hidden(C_515, B_514) | ~r2_hidden(C_515, A_513))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.09/2.93  tff(c_10402, plain, (![C_518]: (~r2_hidden(C_518, '#skF_10') | ~r2_hidden(C_518, k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_10289, c_10374])).
% 8.09/2.93  tff(c_10414, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_10249, c_10402])).
% 8.09/2.93  tff(c_10424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10226, c_10414])).
% 8.09/2.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.93  
% 8.09/2.93  Inference rules
% 8.09/2.93  ----------------------
% 8.09/2.93  #Ref     : 0
% 8.09/2.93  #Sup     : 2390
% 8.09/2.93  #Fact    : 6
% 8.09/2.93  #Define  : 0
% 8.09/2.93  #Split   : 2
% 8.09/2.93  #Chain   : 0
% 8.09/2.93  #Close   : 0
% 8.09/2.93  
% 8.09/2.93  Ordering : KBO
% 8.09/2.93  
% 8.09/2.93  Simplification rules
% 8.09/2.93  ----------------------
% 8.09/2.93  #Subsume      : 330
% 8.09/2.93  #Demod        : 582
% 8.09/2.93  #Tautology    : 537
% 8.09/2.93  #SimpNegUnit  : 103
% 8.09/2.93  #BackRed      : 15
% 8.09/2.93  
% 8.09/2.93  #Partial instantiations: 0
% 8.09/2.93  #Strategies tried      : 1
% 8.09/2.93  
% 8.09/2.93  Timing (in seconds)
% 8.09/2.93  ----------------------
% 8.26/2.93  Preprocessing        : 0.34
% 8.26/2.93  Parsing              : 0.17
% 8.26/2.93  CNF conversion       : 0.03
% 8.26/2.93  Main loop            : 1.81
% 8.26/2.93  Inferencing          : 0.52
% 8.26/2.93  Reduction            : 0.59
% 8.26/2.93  Demodulation         : 0.44
% 8.26/2.93  BG Simplification    : 0.08
% 8.26/2.93  Subsumption          : 0.48
% 8.26/2.93  Abstraction          : 0.10
% 8.26/2.93  MUC search           : 0.00
% 8.26/2.94  Cooper               : 0.00
% 8.26/2.94  Total                : 2.20
% 8.26/2.94  Index Insertion      : 0.00
% 8.26/2.94  Index Deletion       : 0.00
% 8.26/2.94  Index Matching       : 0.00
% 8.26/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
