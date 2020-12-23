%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:09 EST 2020

% Result     : Theorem 6.76s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 281 expanded)
%              Number of leaves         :   48 ( 109 expanded)
%              Depth                    :   11
%              Number of atoms          :  197 ( 519 expanded)
%              Number of equality atoms :   89 ( 326 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_94,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_84,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_92,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(c_76,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_133,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_68,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k1_tarski(A_72),B_73)
      | ~ r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_74,plain,
    ( k1_xboole_0 != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_119,plain,(
    k1_tarski('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_134,plain,(
    ! [A_84,B_85] : r1_tarski(A_84,k2_xboole_0(A_84,B_85)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_137,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_134])).

tff(c_601,plain,(
    ! [B_139,A_140] :
      ( B_139 = A_140
      | ~ r1_tarski(B_139,A_140)
      | ~ r1_tarski(A_140,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_605,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_137,c_601])).

tff(c_613,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_605])).

tff(c_622,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_613])).

tff(c_70,plain,(
    ! [A_74,B_75] :
      ( r1_xboole_0(k1_tarski(A_74),B_75)
      | r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_285,plain,(
    ! [A_100,B_101] :
      ( k3_xboole_0(A_100,B_101) = A_100
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_299,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_137,c_285])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_528,plain,(
    ! [A_128,B_129,C_130] :
      ( ~ r1_xboole_0(A_128,B_129)
      | ~ r2_hidden(C_130,k3_xboole_0(A_128,B_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_623,plain,(
    ! [A_141,B_142] :
      ( ~ r1_xboole_0(A_141,B_142)
      | v1_xboole_0(k3_xboole_0(A_141,B_142)) ) ),
    inference(resolution,[status(thm)],[c_8,c_528])).

tff(c_690,plain,(
    ! [B_150,A_151] :
      ( ~ r1_xboole_0(B_150,A_151)
      | v1_xboole_0(k3_xboole_0(A_151,B_150)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_623])).

tff(c_699,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_690])).

tff(c_710,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_699])).

tff(c_733,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_710])).

tff(c_740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_622,c_733])).

tff(c_741,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_699])).

tff(c_18,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_745,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_741,c_18])).

tff(c_749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_745])).

tff(c_750,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_751,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_50,plain,(
    ! [A_43] : k5_xboole_0(A_43,A_43) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_753,plain,(
    ! [A_43] : k5_xboole_0(A_43,A_43) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_50])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1141,plain,(
    ! [A_200,B_201] : k5_xboole_0(A_200,k3_xboole_0(A_200,B_201)) = k4_xboole_0(A_200,B_201) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1170,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k4_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1141])).

tff(c_1175,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_1170])).

tff(c_46,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1299,plain,(
    ! [A_214,B_215,C_216] :
      ( ~ r1_xboole_0(A_214,B_215)
      | ~ r2_hidden(C_216,k3_xboole_0(A_214,B_215)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1325,plain,(
    ! [A_217,C_218] :
      ( ~ r1_xboole_0(A_217,A_217)
      | ~ r2_hidden(C_218,A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1299])).

tff(c_1328,plain,(
    ! [C_218,B_39] :
      ( ~ r2_hidden(C_218,B_39)
      | k4_xboole_0(B_39,B_39) != B_39 ) ),
    inference(resolution,[status(thm)],[c_46,c_1325])).

tff(c_1337,plain,(
    ! [C_219,B_220] :
      ( ~ r2_hidden(C_219,B_220)
      | B_220 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_1328])).

tff(c_1356,plain,(
    ! [A_222] :
      ( A_222 != '#skF_5'
      | v1_xboole_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_8,c_1337])).

tff(c_1266,plain,(
    ! [A_208,B_209] :
      ( r2_hidden('#skF_2'(A_208,B_209),A_208)
      | r1_tarski(A_208,B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1277,plain,(
    ! [A_210,B_211] :
      ( ~ v1_xboole_0(A_210)
      | r1_tarski(A_210,B_211) ) ),
    inference(resolution,[status(thm)],[c_1266,c_6])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1296,plain,(
    ! [A_210,B_211] :
      ( k2_xboole_0(A_210,B_211) = B_211
      | ~ v1_xboole_0(A_210) ) ),
    inference(resolution,[status(thm)],[c_1277,c_34])).

tff(c_1527,plain,(
    ! [B_211] : k2_xboole_0('#skF_5',B_211) = B_211 ),
    inference(resolution,[status(thm)],[c_1356,c_1296])).

tff(c_1529,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1527,c_80])).

tff(c_1531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_750,c_1529])).

tff(c_1533,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1603,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1533,c_1533,c_78])).

tff(c_1532,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1538,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1533,c_80])).

tff(c_28,plain,(
    ! [B_23] : r1_tarski(B_23,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1758,plain,(
    ! [A_265,B_266] :
      ( r2_hidden(A_265,B_266)
      | ~ r1_tarski(k1_tarski(A_265),B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1781,plain,(
    ! [A_269] : r2_hidden(A_269,k1_tarski(A_269)) ),
    inference(resolution,[status(thm)],[c_28,c_1758])).

tff(c_1789,plain,(
    ! [A_270] : ~ v1_xboole_0(k1_tarski(A_270)) ),
    inference(resolution,[status(thm)],[c_1781,c_6])).

tff(c_1791,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_1789])).

tff(c_42,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1711,plain,(
    ! [A_254,B_255] :
      ( k3_xboole_0(A_254,B_255) = A_254
      | ~ r1_tarski(A_254,B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1718,plain,(
    ! [A_36,B_37] : k3_xboole_0(A_36,k2_xboole_0(A_36,B_37)) = A_36 ),
    inference(resolution,[status(thm)],[c_42,c_1711])).

tff(c_2111,plain,(
    ! [A_305,B_306,C_307] :
      ( ~ r1_xboole_0(A_305,B_306)
      | ~ r2_hidden(C_307,k3_xboole_0(A_305,B_306)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2773,plain,(
    ! [A_349,B_350] :
      ( ~ r1_xboole_0(A_349,B_350)
      | v1_xboole_0(k3_xboole_0(A_349,B_350)) ) ),
    inference(resolution,[status(thm)],[c_8,c_2111])).

tff(c_4227,plain,(
    ! [A_405,B_406] :
      ( ~ r1_xboole_0(A_405,k2_xboole_0(A_405,B_406))
      | v1_xboole_0(A_405) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1718,c_2773])).

tff(c_4262,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1538,c_4227])).

tff(c_4277,plain,(
    ~ r1_xboole_0('#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1791,c_4262])).

tff(c_1739,plain,(
    ! [A_260,B_261] :
      ( r1_xboole_0(k1_tarski(A_260),B_261)
      | r2_hidden(A_260,B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1745,plain,(
    ! [B_261] :
      ( r1_xboole_0('#skF_5',B_261)
      | r2_hidden('#skF_4',B_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_1739])).

tff(c_1898,plain,(
    ! [A_283,B_284] :
      ( r1_tarski(k1_tarski(A_283),B_284)
      | ~ r2_hidden(A_283,B_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1914,plain,(
    ! [B_285] :
      ( r1_tarski('#skF_5',B_285)
      | ~ r2_hidden('#skF_4',B_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_1898])).

tff(c_1944,plain,(
    ! [B_261] :
      ( r1_tarski('#skF_5',B_261)
      | r1_xboole_0('#skF_5',B_261) ) ),
    inference(resolution,[status(thm)],[c_1745,c_1914])).

tff(c_4120,plain,(
    ! [B_397,A_398] :
      ( ~ r1_xboole_0(B_397,A_398)
      | v1_xboole_0(k3_xboole_0(A_398,B_397)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2773])).

tff(c_4521,plain,(
    ! [A_421,B_422] :
      ( k3_xboole_0(A_421,B_422) = k1_xboole_0
      | ~ r1_xboole_0(B_422,A_421) ) ),
    inference(resolution,[status(thm)],[c_4120,c_18])).

tff(c_4725,plain,(
    ! [B_428] :
      ( k3_xboole_0(B_428,'#skF_5') = k1_xboole_0
      | r1_tarski('#skF_5',B_428) ) ),
    inference(resolution,[status(thm)],[c_1944,c_4521])).

tff(c_2538,plain,(
    ! [C_332,B_333,A_334] :
      ( r2_hidden(C_332,B_333)
      | ~ r2_hidden(C_332,A_334)
      | ~ r1_tarski(A_334,B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2561,plain,(
    ! [B_333,B_261] :
      ( r2_hidden('#skF_4',B_333)
      | ~ r1_tarski(B_261,B_333)
      | r1_xboole_0('#skF_5',B_261) ) ),
    inference(resolution,[status(thm)],[c_1745,c_2538])).

tff(c_4729,plain,(
    ! [B_428] :
      ( r2_hidden('#skF_4',B_428)
      | r1_xboole_0('#skF_5','#skF_5')
      | k3_xboole_0(B_428,'#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4725,c_2561])).

tff(c_4755,plain,(
    ! [B_428] :
      ( r2_hidden('#skF_4',B_428)
      | k3_xboole_0(B_428,'#skF_5') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_4277,c_4729])).

tff(c_6354,plain,(
    ! [A_494,B_495] :
      ( k2_xboole_0(k1_tarski(A_494),B_495) = B_495
      | ~ r2_hidden(A_494,B_495) ) ),
    inference(resolution,[status(thm)],[c_1898,c_34])).

tff(c_6438,plain,(
    ! [B_496] :
      ( k2_xboole_0('#skF_5',B_496) = B_496
      | ~ r2_hidden('#skF_4',B_496) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_6354])).

tff(c_9960,plain,(
    ! [B_563] :
      ( k2_xboole_0('#skF_5',B_563) = B_563
      | k3_xboole_0(B_563,'#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4755,c_6438])).

tff(c_3866,plain,(
    ! [A_386,B_387,C_388] : k3_xboole_0(k3_xboole_0(A_386,B_387),C_388) = k3_xboole_0(A_386,k3_xboole_0(B_387,C_388)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5907,plain,(
    ! [A_481,C_482] : k3_xboole_0(A_481,k3_xboole_0(A_481,C_482)) = k3_xboole_0(A_481,C_482) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3866])).

tff(c_6021,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5907])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1604,plain,(
    ! [B_247,A_248] : k5_xboole_0(B_247,A_248) = k5_xboole_0(A_248,B_247) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_35] : k5_xboole_0(A_35,k1_xboole_0) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1620,plain,(
    ! [A_248] : k5_xboole_0(k1_xboole_0,A_248) = A_248 ),
    inference(superposition,[status(thm),theory(equality)],[c_1604,c_40])).

tff(c_2951,plain,(
    ! [A_356,B_357,C_358] : k5_xboole_0(k5_xboole_0(A_356,B_357),C_358) = k5_xboole_0(A_356,k5_xboole_0(B_357,C_358)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3008,plain,(
    ! [A_43,C_358] : k5_xboole_0(A_43,k5_xboole_0(A_43,C_358)) = k5_xboole_0(k1_xboole_0,C_358) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2951])).

tff(c_3029,plain,(
    ! [A_359,C_360] : k5_xboole_0(A_359,k5_xboole_0(A_359,C_360)) = C_360 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_3008])).

tff(c_3072,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3029])).

tff(c_3638,plain,(
    ! [A_373,B_374] : k4_xboole_0(k2_xboole_0(A_373,B_374),k3_xboole_0(A_373,B_374)) = k5_xboole_0(A_373,B_374) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3683,plain,(
    k4_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_6')) = k5_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1538,c_3638])).

tff(c_3691,plain,(
    k4_xboole_0('#skF_5',k3_xboole_0('#skF_6','#skF_5')) = k5_xboole_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_3683])).

tff(c_32,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9520,plain,(
    ! [A_558,B_559] : k5_xboole_0(A_558,k4_xboole_0(A_558,B_559)) = k3_xboole_0(A_558,B_559) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3029])).

tff(c_9570,plain,(
    k5_xboole_0('#skF_5',k5_xboole_0('#skF_6','#skF_5')) = k3_xboole_0('#skF_5',k3_xboole_0('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3691,c_9520])).

tff(c_9608,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6021,c_3072,c_9570])).

tff(c_9973,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_9960,c_9608])).

tff(c_10129,plain,
    ( k1_xboole_0 = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1538,c_9973])).

tff(c_10131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1603,c_1532,c_10129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:32:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.76/2.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.45  
% 6.76/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 6.76/2.45  
% 6.76/2.45  %Foreground sorts:
% 6.76/2.45  
% 6.76/2.45  
% 6.76/2.45  %Background operators:
% 6.76/2.45  
% 6.76/2.45  
% 6.76/2.45  %Foreground operators:
% 6.76/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.76/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.76/2.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.76/2.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.76/2.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.76/2.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.76/2.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.76/2.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.76/2.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.76/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.76/2.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.76/2.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.76/2.45  tff('#skF_5', type, '#skF_5': $i).
% 6.76/2.45  tff('#skF_6', type, '#skF_6': $i).
% 6.76/2.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.76/2.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.76/2.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.76/2.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.76/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.76/2.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.76/2.45  tff('#skF_4', type, '#skF_4': $i).
% 6.76/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.76/2.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.76/2.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.76/2.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.76/2.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.76/2.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.76/2.45  
% 6.95/2.47  tff(f_138, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 6.95/2.47  tff(f_112, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.95/2.47  tff(f_86, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.95/2.47  tff(f_68, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.95/2.47  tff(f_117, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.95/2.47  tff(f_82, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.95/2.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.95/2.47  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.95/2.47  tff(f_62, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.95/2.47  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.95/2.47  tff(f_94, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.95/2.47  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.95/2.47  tff(f_72, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.95/2.47  tff(f_90, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.95/2.47  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.95/2.47  tff(f_76, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.95/2.47  tff(f_78, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.95/2.47  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.95/2.47  tff(f_84, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.95/2.47  tff(f_92, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.95/2.47  tff(f_70, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 6.95/2.47  tff(c_76, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.95/2.47  tff(c_133, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_76])).
% 6.95/2.47  tff(c_68, plain, (![A_72, B_73]: (r1_tarski(k1_tarski(A_72), B_73) | ~r2_hidden(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.95/2.47  tff(c_74, plain, (k1_xboole_0!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.95/2.47  tff(c_119, plain, (k1_tarski('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_74])).
% 6.95/2.47  tff(c_80, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.95/2.47  tff(c_134, plain, (![A_84, B_85]: (r1_tarski(A_84, k2_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.95/2.47  tff(c_137, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_134])).
% 6.95/2.47  tff(c_601, plain, (![B_139, A_140]: (B_139=A_140 | ~r1_tarski(B_139, A_140) | ~r1_tarski(A_140, B_139))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.95/2.47  tff(c_605, plain, (k1_tarski('#skF_4')='#skF_5' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_137, c_601])).
% 6.95/2.47  tff(c_613, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_119, c_605])).
% 6.95/2.47  tff(c_622, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_613])).
% 6.95/2.47  tff(c_70, plain, (![A_74, B_75]: (r1_xboole_0(k1_tarski(A_74), B_75) | r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.95/2.47  tff(c_285, plain, (![A_100, B_101]: (k3_xboole_0(A_100, B_101)=A_100 | ~r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.95/2.47  tff(c_299, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_137, c_285])).
% 6.95/2.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.95/2.47  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.95/2.47  tff(c_528, plain, (![A_128, B_129, C_130]: (~r1_xboole_0(A_128, B_129) | ~r2_hidden(C_130, k3_xboole_0(A_128, B_129)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.95/2.47  tff(c_623, plain, (![A_141, B_142]: (~r1_xboole_0(A_141, B_142) | v1_xboole_0(k3_xboole_0(A_141, B_142)))), inference(resolution, [status(thm)], [c_8, c_528])).
% 6.95/2.47  tff(c_690, plain, (![B_150, A_151]: (~r1_xboole_0(B_150, A_151) | v1_xboole_0(k3_xboole_0(A_151, B_150)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_623])).
% 6.95/2.47  tff(c_699, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_299, c_690])).
% 6.95/2.47  tff(c_710, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_699])).
% 6.95/2.47  tff(c_733, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_710])).
% 6.95/2.47  tff(c_740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_622, c_733])).
% 6.95/2.47  tff(c_741, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_699])).
% 6.95/2.47  tff(c_18, plain, (![A_16]: (k1_xboole_0=A_16 | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.95/2.47  tff(c_745, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_741, c_18])).
% 6.95/2.47  tff(c_749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_745])).
% 6.95/2.47  tff(c_750, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_76])).
% 6.95/2.47  tff(c_751, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_76])).
% 6.95/2.47  tff(c_50, plain, (![A_43]: (k5_xboole_0(A_43, A_43)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.95/2.47  tff(c_753, plain, (![A_43]: (k5_xboole_0(A_43, A_43)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_751, c_50])).
% 6.95/2.47  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.95/2.47  tff(c_1141, plain, (![A_200, B_201]: (k5_xboole_0(A_200, k3_xboole_0(A_200, B_201))=k4_xboole_0(A_200, B_201))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.95/2.47  tff(c_1170, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k4_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1141])).
% 6.95/2.47  tff(c_1175, plain, (![A_14]: (k4_xboole_0(A_14, A_14)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_753, c_1170])).
% 6.95/2.47  tff(c_46, plain, (![A_38, B_39]: (r1_xboole_0(A_38, B_39) | k4_xboole_0(A_38, B_39)!=A_38)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.95/2.47  tff(c_1299, plain, (![A_214, B_215, C_216]: (~r1_xboole_0(A_214, B_215) | ~r2_hidden(C_216, k3_xboole_0(A_214, B_215)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.95/2.47  tff(c_1325, plain, (![A_217, C_218]: (~r1_xboole_0(A_217, A_217) | ~r2_hidden(C_218, A_217))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1299])).
% 6.95/2.47  tff(c_1328, plain, (![C_218, B_39]: (~r2_hidden(C_218, B_39) | k4_xboole_0(B_39, B_39)!=B_39)), inference(resolution, [status(thm)], [c_46, c_1325])).
% 6.95/2.47  tff(c_1337, plain, (![C_219, B_220]: (~r2_hidden(C_219, B_220) | B_220!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_1328])).
% 6.95/2.47  tff(c_1356, plain, (![A_222]: (A_222!='#skF_5' | v1_xboole_0(A_222))), inference(resolution, [status(thm)], [c_8, c_1337])).
% 6.95/2.47  tff(c_1266, plain, (![A_208, B_209]: (r2_hidden('#skF_2'(A_208, B_209), A_208) | r1_tarski(A_208, B_209))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.95/2.47  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.95/2.47  tff(c_1277, plain, (![A_210, B_211]: (~v1_xboole_0(A_210) | r1_tarski(A_210, B_211))), inference(resolution, [status(thm)], [c_1266, c_6])).
% 6.95/2.47  tff(c_34, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.95/2.47  tff(c_1296, plain, (![A_210, B_211]: (k2_xboole_0(A_210, B_211)=B_211 | ~v1_xboole_0(A_210))), inference(resolution, [status(thm)], [c_1277, c_34])).
% 6.95/2.47  tff(c_1527, plain, (![B_211]: (k2_xboole_0('#skF_5', B_211)=B_211)), inference(resolution, [status(thm)], [c_1356, c_1296])).
% 6.95/2.47  tff(c_1529, plain, (k1_tarski('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1527, c_80])).
% 6.95/2.47  tff(c_1531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_750, c_1529])).
% 6.95/2.47  tff(c_1533, plain, (k1_tarski('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_74])).
% 6.95/2.47  tff(c_78, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.95/2.47  tff(c_1603, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1533, c_1533, c_78])).
% 6.95/2.47  tff(c_1532, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_74])).
% 6.95/2.47  tff(c_1538, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1533, c_80])).
% 6.95/2.47  tff(c_28, plain, (![B_23]: (r1_tarski(B_23, B_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.95/2.47  tff(c_1758, plain, (![A_265, B_266]: (r2_hidden(A_265, B_266) | ~r1_tarski(k1_tarski(A_265), B_266))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.95/2.47  tff(c_1781, plain, (![A_269]: (r2_hidden(A_269, k1_tarski(A_269)))), inference(resolution, [status(thm)], [c_28, c_1758])).
% 6.95/2.47  tff(c_1789, plain, (![A_270]: (~v1_xboole_0(k1_tarski(A_270)))), inference(resolution, [status(thm)], [c_1781, c_6])).
% 6.95/2.47  tff(c_1791, plain, (~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1533, c_1789])).
% 6.95/2.47  tff(c_42, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.95/2.47  tff(c_1711, plain, (![A_254, B_255]: (k3_xboole_0(A_254, B_255)=A_254 | ~r1_tarski(A_254, B_255))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.95/2.47  tff(c_1718, plain, (![A_36, B_37]: (k3_xboole_0(A_36, k2_xboole_0(A_36, B_37))=A_36)), inference(resolution, [status(thm)], [c_42, c_1711])).
% 6.95/2.47  tff(c_2111, plain, (![A_305, B_306, C_307]: (~r1_xboole_0(A_305, B_306) | ~r2_hidden(C_307, k3_xboole_0(A_305, B_306)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.95/2.47  tff(c_2773, plain, (![A_349, B_350]: (~r1_xboole_0(A_349, B_350) | v1_xboole_0(k3_xboole_0(A_349, B_350)))), inference(resolution, [status(thm)], [c_8, c_2111])).
% 6.95/2.47  tff(c_4227, plain, (![A_405, B_406]: (~r1_xboole_0(A_405, k2_xboole_0(A_405, B_406)) | v1_xboole_0(A_405))), inference(superposition, [status(thm), theory('equality')], [c_1718, c_2773])).
% 6.95/2.47  tff(c_4262, plain, (~r1_xboole_0('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1538, c_4227])).
% 6.95/2.47  tff(c_4277, plain, (~r1_xboole_0('#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1791, c_4262])).
% 6.95/2.47  tff(c_1739, plain, (![A_260, B_261]: (r1_xboole_0(k1_tarski(A_260), B_261) | r2_hidden(A_260, B_261))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.95/2.47  tff(c_1745, plain, (![B_261]: (r1_xboole_0('#skF_5', B_261) | r2_hidden('#skF_4', B_261))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_1739])).
% 6.95/2.47  tff(c_1898, plain, (![A_283, B_284]: (r1_tarski(k1_tarski(A_283), B_284) | ~r2_hidden(A_283, B_284))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.95/2.47  tff(c_1914, plain, (![B_285]: (r1_tarski('#skF_5', B_285) | ~r2_hidden('#skF_4', B_285))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_1898])).
% 6.95/2.47  tff(c_1944, plain, (![B_261]: (r1_tarski('#skF_5', B_261) | r1_xboole_0('#skF_5', B_261))), inference(resolution, [status(thm)], [c_1745, c_1914])).
% 6.95/2.47  tff(c_4120, plain, (![B_397, A_398]: (~r1_xboole_0(B_397, A_398) | v1_xboole_0(k3_xboole_0(A_398, B_397)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2773])).
% 6.95/2.47  tff(c_4521, plain, (![A_421, B_422]: (k3_xboole_0(A_421, B_422)=k1_xboole_0 | ~r1_xboole_0(B_422, A_421))), inference(resolution, [status(thm)], [c_4120, c_18])).
% 6.95/2.47  tff(c_4725, plain, (![B_428]: (k3_xboole_0(B_428, '#skF_5')=k1_xboole_0 | r1_tarski('#skF_5', B_428))), inference(resolution, [status(thm)], [c_1944, c_4521])).
% 6.95/2.47  tff(c_2538, plain, (![C_332, B_333, A_334]: (r2_hidden(C_332, B_333) | ~r2_hidden(C_332, A_334) | ~r1_tarski(A_334, B_333))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.95/2.47  tff(c_2561, plain, (![B_333, B_261]: (r2_hidden('#skF_4', B_333) | ~r1_tarski(B_261, B_333) | r1_xboole_0('#skF_5', B_261))), inference(resolution, [status(thm)], [c_1745, c_2538])).
% 6.95/2.47  tff(c_4729, plain, (![B_428]: (r2_hidden('#skF_4', B_428) | r1_xboole_0('#skF_5', '#skF_5') | k3_xboole_0(B_428, '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_4725, c_2561])).
% 6.95/2.47  tff(c_4755, plain, (![B_428]: (r2_hidden('#skF_4', B_428) | k3_xboole_0(B_428, '#skF_5')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_4277, c_4729])).
% 6.95/2.47  tff(c_6354, plain, (![A_494, B_495]: (k2_xboole_0(k1_tarski(A_494), B_495)=B_495 | ~r2_hidden(A_494, B_495))), inference(resolution, [status(thm)], [c_1898, c_34])).
% 6.95/2.47  tff(c_6438, plain, (![B_496]: (k2_xboole_0('#skF_5', B_496)=B_496 | ~r2_hidden('#skF_4', B_496))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_6354])).
% 6.95/2.47  tff(c_9960, plain, (![B_563]: (k2_xboole_0('#skF_5', B_563)=B_563 | k3_xboole_0(B_563, '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_4755, c_6438])).
% 6.95/2.47  tff(c_3866, plain, (![A_386, B_387, C_388]: (k3_xboole_0(k3_xboole_0(A_386, B_387), C_388)=k3_xboole_0(A_386, k3_xboole_0(B_387, C_388)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.95/2.47  tff(c_5907, plain, (![A_481, C_482]: (k3_xboole_0(A_481, k3_xboole_0(A_481, C_482))=k3_xboole_0(A_481, C_482))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3866])).
% 6.95/2.47  tff(c_6021, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5907])).
% 6.95/2.47  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.95/2.47  tff(c_1604, plain, (![B_247, A_248]: (k5_xboole_0(B_247, A_248)=k5_xboole_0(A_248, B_247))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.95/2.47  tff(c_40, plain, (![A_35]: (k5_xboole_0(A_35, k1_xboole_0)=A_35)), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.95/2.47  tff(c_1620, plain, (![A_248]: (k5_xboole_0(k1_xboole_0, A_248)=A_248)), inference(superposition, [status(thm), theory('equality')], [c_1604, c_40])).
% 6.95/2.47  tff(c_2951, plain, (![A_356, B_357, C_358]: (k5_xboole_0(k5_xboole_0(A_356, B_357), C_358)=k5_xboole_0(A_356, k5_xboole_0(B_357, C_358)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.95/2.47  tff(c_3008, plain, (![A_43, C_358]: (k5_xboole_0(A_43, k5_xboole_0(A_43, C_358))=k5_xboole_0(k1_xboole_0, C_358))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2951])).
% 6.95/2.47  tff(c_3029, plain, (![A_359, C_360]: (k5_xboole_0(A_359, k5_xboole_0(A_359, C_360))=C_360)), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_3008])).
% 6.95/2.47  tff(c_3072, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_3029])).
% 6.95/2.47  tff(c_3638, plain, (![A_373, B_374]: (k4_xboole_0(k2_xboole_0(A_373, B_374), k3_xboole_0(A_373, B_374))=k5_xboole_0(A_373, B_374))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.95/2.47  tff(c_3683, plain, (k4_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_6'))=k5_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1538, c_3638])).
% 6.95/2.47  tff(c_3691, plain, (k4_xboole_0('#skF_5', k3_xboole_0('#skF_6', '#skF_5'))=k5_xboole_0('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_3683])).
% 6.95/2.47  tff(c_32, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.95/2.47  tff(c_9520, plain, (![A_558, B_559]: (k5_xboole_0(A_558, k4_xboole_0(A_558, B_559))=k3_xboole_0(A_558, B_559))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3029])).
% 6.95/2.47  tff(c_9570, plain, (k5_xboole_0('#skF_5', k5_xboole_0('#skF_6', '#skF_5'))=k3_xboole_0('#skF_5', k3_xboole_0('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3691, c_9520])).
% 6.95/2.47  tff(c_9608, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6021, c_3072, c_9570])).
% 6.95/2.47  tff(c_9973, plain, (k1_xboole_0='#skF_6' | k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_9960, c_9608])).
% 6.95/2.47  tff(c_10129, plain, (k1_xboole_0='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1538, c_9973])).
% 6.95/2.47  tff(c_10131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1603, c_1532, c_10129])).
% 6.95/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.47  
% 6.95/2.47  Inference rules
% 6.95/2.47  ----------------------
% 6.95/2.47  #Ref     : 1
% 6.95/2.47  #Sup     : 2404
% 6.95/2.47  #Fact    : 0
% 6.95/2.47  #Define  : 0
% 6.95/2.47  #Split   : 7
% 6.95/2.47  #Chain   : 0
% 6.95/2.47  #Close   : 0
% 6.95/2.47  
% 6.95/2.47  Ordering : KBO
% 6.95/2.47  
% 6.95/2.47  Simplification rules
% 6.95/2.47  ----------------------
% 6.95/2.47  #Subsume      : 743
% 6.95/2.47  #Demod        : 837
% 6.95/2.47  #Tautology    : 799
% 6.95/2.47  #SimpNegUnit  : 142
% 6.95/2.47  #BackRed      : 11
% 6.95/2.47  
% 6.95/2.47  #Partial instantiations: 0
% 6.95/2.47  #Strategies tried      : 1
% 6.95/2.47  
% 6.95/2.47  Timing (in seconds)
% 6.95/2.47  ----------------------
% 6.95/2.48  Preprocessing        : 0.35
% 6.95/2.48  Parsing              : 0.18
% 6.95/2.48  CNF conversion       : 0.02
% 6.95/2.48  Main loop            : 1.35
% 6.95/2.48  Inferencing          : 0.44
% 6.95/2.48  Reduction            : 0.52
% 6.95/2.48  Demodulation         : 0.40
% 6.95/2.48  BG Simplification    : 0.05
% 6.95/2.48  Subsumption          : 0.26
% 6.95/2.48  Abstraction          : 0.06
% 6.95/2.48  MUC search           : 0.00
% 6.95/2.48  Cooper               : 0.00
% 6.95/2.48  Total                : 1.75
% 6.95/2.48  Index Insertion      : 0.00
% 6.95/2.48  Index Deletion       : 0.00
% 6.95/2.48  Index Matching       : 0.00
% 6.95/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
