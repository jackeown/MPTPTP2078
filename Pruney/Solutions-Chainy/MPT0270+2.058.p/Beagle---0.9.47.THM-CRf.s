%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:00 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 261 expanded)
%              Number of leaves         :   32 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  147 ( 438 expanded)
%              Number of equality atoms :   38 ( 136 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_105,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_24,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_44,B_45] :
      ( r1_xboole_0(k1_tarski(A_44),B_45)
      | r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_2'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_146,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(C_65,k3_xboole_0(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_158,plain,(
    ! [A_66,B_67] :
      ( ~ r1_xboole_0(A_66,B_67)
      | k3_xboole_0(A_66,B_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_146])).

tff(c_217,plain,(
    ! [A_78,B_79] :
      ( k3_xboole_0(k1_tarski(A_78),B_79) = k1_xboole_0
      | r2_hidden(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_40,c_158])).

tff(c_22,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_232,plain,(
    ! [A_78,B_79] :
      ( k5_xboole_0(k1_tarski(A_78),k1_xboole_0) = k4_xboole_0(k1_tarski(A_78),B_79)
      | r2_hidden(A_78,B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_22])).

tff(c_338,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(k1_tarski(A_88),B_89) = k1_tarski(A_88)
      | r2_hidden(A_88,B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_232])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_131,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_352,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_131])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_352])).

tff(c_367,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_368,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_543,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_50])).

tff(c_681,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden(A_131,B_132)
      | ~ r2_hidden(A_131,C_133)
      | r2_hidden(A_131,k5_xboole_0(B_132,C_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_768,plain,(
    ! [A_156,A_157,B_158] :
      ( r2_hidden(A_156,A_157)
      | ~ r2_hidden(A_156,k3_xboole_0(A_157,B_158))
      | r2_hidden(A_156,k4_xboole_0(A_157,B_158)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_681])).

tff(c_774,plain,(
    ! [A_156] :
      ( r2_hidden(A_156,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_156,k3_xboole_0(k1_tarski('#skF_5'),'#skF_6'))
      | r2_hidden(A_156,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_768])).

tff(c_1014,plain,(
    ! [A_173] :
      ( r2_hidden(A_173,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_173,k3_xboole_0('#skF_6',k1_tarski('#skF_5')))
      | r2_hidden(A_173,k1_tarski('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_774])).

tff(c_1031,plain,
    ( r2_hidden('#skF_1'('#skF_6',k1_tarski('#skF_5')),k1_tarski('#skF_5'))
    | r1_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_1014])).

tff(c_1035,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1031])).

tff(c_373,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,k3_xboole_0(A_90,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_404,plain,(
    ! [B_99,A_100,C_101] :
      ( ~ r1_xboole_0(B_99,A_100)
      | ~ r2_hidden(C_101,k3_xboole_0(A_100,B_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_373])).

tff(c_415,plain,(
    ! [B_99,A_100] :
      ( ~ r1_xboole_0(B_99,A_100)
      | k3_xboole_0(A_100,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_404])).

tff(c_1045,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1035,c_415])).

tff(c_116,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_128,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_1071,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_128])).

tff(c_1104,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1071])).

tff(c_42,plain,(
    ! [B_47,A_46] :
      ( ~ r2_hidden(B_47,A_46)
      | k4_xboole_0(A_46,k1_tarski(B_47)) != A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1207,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1104,c_42])).

tff(c_1225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_1207])).

tff(c_1227,plain,(
    ~ r1_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1031])).

tff(c_1226,plain,(
    r2_hidden('#skF_1'('#skF_6',k1_tarski('#skF_5')),k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1031])).

tff(c_634,plain,(
    ! [A_123,C_124,B_125] :
      ( ~ r2_hidden(A_123,C_124)
      | ~ r2_hidden(A_123,B_125)
      | ~ r2_hidden(A_123,k5_xboole_0(B_125,C_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1240,plain,(
    ! [A_177,A_178,B_179] :
      ( ~ r2_hidden(A_177,k3_xboole_0(A_178,B_179))
      | ~ r2_hidden(A_177,A_178)
      | ~ r2_hidden(A_177,k4_xboole_0(A_178,B_179)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_634])).

tff(c_1255,plain,(
    ! [A_177] :
      ( ~ r2_hidden(A_177,k3_xboole_0(k1_tarski('#skF_5'),'#skF_6'))
      | ~ r2_hidden(A_177,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_177,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_1240])).

tff(c_1288,plain,(
    ! [A_180] :
      ( ~ r2_hidden(A_180,k3_xboole_0('#skF_6',k1_tarski('#skF_5')))
      | ~ r2_hidden(A_180,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_180,k1_tarski('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1255])).

tff(c_1296,plain,
    ( ~ r2_hidden('#skF_1'('#skF_6',k1_tarski('#skF_5')),k1_tarski('#skF_5'))
    | r1_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_1288])).

tff(c_1307,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1226,c_1296])).

tff(c_1309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1227,c_1307])).

tff(c_1310,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1311,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1508,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1311,c_52])).

tff(c_1643,plain,(
    ! [A_231,C_232,B_233] :
      ( ~ r2_hidden(A_231,C_232)
      | ~ r2_hidden(A_231,B_233)
      | ~ r2_hidden(A_231,k5_xboole_0(B_233,C_232)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1729,plain,(
    ! [A_254,A_255,B_256] :
      ( ~ r2_hidden(A_254,k3_xboole_0(A_255,B_256))
      | ~ r2_hidden(A_254,A_255)
      | ~ r2_hidden(A_254,k4_xboole_0(A_255,B_256)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1643])).

tff(c_1738,plain,(
    ! [A_254] :
      ( ~ r2_hidden(A_254,k3_xboole_0(k1_tarski('#skF_5'),'#skF_6'))
      | ~ r2_hidden(A_254,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_254,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1508,c_1729])).

tff(c_1788,plain,(
    ! [A_263] :
      ( ~ r2_hidden(A_263,k3_xboole_0('#skF_6',k1_tarski('#skF_5')))
      | ~ r2_hidden(A_263,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_263,k1_tarski('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1738])).

tff(c_1805,plain,
    ( ~ r2_hidden('#skF_1'('#skF_6',k1_tarski('#skF_5')),k1_tarski('#skF_5'))
    | r1_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_1788])).

tff(c_1809,plain,(
    ~ r2_hidden('#skF_1'('#skF_6',k1_tarski('#skF_5')),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1805])).

tff(c_1322,plain,(
    ! [A_185,B_186] : k5_xboole_0(A_185,k3_xboole_0(A_185,B_186)) = k4_xboole_0(A_185,B_186) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1334,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1322])).

tff(c_1682,plain,(
    ! [A_237,B_238,C_239] :
      ( r2_hidden(A_237,B_238)
      | ~ r2_hidden(A_237,C_239)
      | r2_hidden(A_237,k5_xboole_0(B_238,C_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1810,plain,(
    ! [A_264,B_265,A_266] :
      ( r2_hidden(A_264,B_265)
      | ~ r2_hidden(A_264,k3_xboole_0(A_266,B_265))
      | r2_hidden(A_264,k4_xboole_0(B_265,A_266)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_1682])).

tff(c_1917,plain,(
    ! [A_283] :
      ( r2_hidden(A_283,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_283,k3_xboole_0('#skF_6',k1_tarski('#skF_5')))
      | r2_hidden(A_283,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1508,c_1810])).

tff(c_1925,plain,
    ( r2_hidden('#skF_1'('#skF_6',k1_tarski('#skF_5')),k1_tarski('#skF_5'))
    | r1_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_1917])).

tff(c_1938,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1809,c_1809,c_1925])).

tff(c_1337,plain,(
    ! [A_187,B_188,C_189] :
      ( ~ r1_xboole_0(A_187,B_188)
      | ~ r2_hidden(C_189,k3_xboole_0(A_187,B_188)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1348,plain,(
    ! [A_187,B_188] :
      ( ~ r1_xboole_0(A_187,B_188)
      | k3_xboole_0(A_187,B_188) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_1337])).

tff(c_1963,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1938,c_1348])).

tff(c_1988,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1963,c_22])).

tff(c_2005,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1988])).

tff(c_2233,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2005,c_42])).

tff(c_2256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_2233])).

tff(c_2257,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1805])).

tff(c_2291,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2257,c_1348])).

tff(c_2382,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2291,c_22])).

tff(c_2399,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2382])).

tff(c_2435,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2399,c_42])).

tff(c_2452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_2435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.65  
% 3.73/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.65  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.73/1.65  
% 3.73/1.65  %Foreground sorts:
% 3.73/1.65  
% 3.73/1.65  
% 3.73/1.65  %Background operators:
% 3.73/1.65  
% 3.73/1.65  
% 3.73/1.65  %Foreground operators:
% 3.73/1.65  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.73/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.73/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.73/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.73/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.73/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.73/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.73/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.73/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.73/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.73/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.73/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.73/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.73/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.73/1.65  
% 3.73/1.67  tff(f_90, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 3.73/1.67  tff(f_60, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.73/1.67  tff(f_79, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.73/1.67  tff(f_56, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.73/1.67  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.73/1.67  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.73/1.67  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.73/1.67  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.73/1.67  tff(f_84, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.73/1.67  tff(c_48, plain, (~r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.73/1.67  tff(c_105, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 3.73/1.67  tff(c_24, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.73/1.67  tff(c_40, plain, (![A_44, B_45]: (r1_xboole_0(k1_tarski(A_44), B_45) | r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.73/1.67  tff(c_20, plain, (![A_11]: (r2_hidden('#skF_2'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.73/1.67  tff(c_146, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(C_65, k3_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.73/1.67  tff(c_158, plain, (![A_66, B_67]: (~r1_xboole_0(A_66, B_67) | k3_xboole_0(A_66, B_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_146])).
% 3.73/1.67  tff(c_217, plain, (![A_78, B_79]: (k3_xboole_0(k1_tarski(A_78), B_79)=k1_xboole_0 | r2_hidden(A_78, B_79))), inference(resolution, [status(thm)], [c_40, c_158])).
% 3.73/1.67  tff(c_22, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.73/1.67  tff(c_232, plain, (![A_78, B_79]: (k5_xboole_0(k1_tarski(A_78), k1_xboole_0)=k4_xboole_0(k1_tarski(A_78), B_79) | r2_hidden(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_217, c_22])).
% 3.73/1.67  tff(c_338, plain, (![A_88, B_89]: (k4_xboole_0(k1_tarski(A_88), B_89)=k1_tarski(A_88) | r2_hidden(A_88, B_89))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_232])).
% 3.73/1.67  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.73/1.67  tff(c_131, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 3.73/1.67  tff(c_352, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_338, c_131])).
% 3.73/1.67  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_352])).
% 3.73/1.67  tff(c_367, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_46])).
% 3.73/1.67  tff(c_16, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.73/1.67  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.73/1.67  tff(c_368, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 3.73/1.67  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.73/1.67  tff(c_543, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_50])).
% 3.73/1.67  tff(c_681, plain, (![A_131, B_132, C_133]: (r2_hidden(A_131, B_132) | ~r2_hidden(A_131, C_133) | r2_hidden(A_131, k5_xboole_0(B_132, C_133)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.73/1.67  tff(c_768, plain, (![A_156, A_157, B_158]: (r2_hidden(A_156, A_157) | ~r2_hidden(A_156, k3_xboole_0(A_157, B_158)) | r2_hidden(A_156, k4_xboole_0(A_157, B_158)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_681])).
% 3.73/1.67  tff(c_774, plain, (![A_156]: (r2_hidden(A_156, k1_tarski('#skF_5')) | ~r2_hidden(A_156, k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')) | r2_hidden(A_156, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_543, c_768])).
% 3.73/1.67  tff(c_1014, plain, (![A_173]: (r2_hidden(A_173, k1_tarski('#skF_5')) | ~r2_hidden(A_173, k3_xboole_0('#skF_6', k1_tarski('#skF_5'))) | r2_hidden(A_173, k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_774])).
% 3.73/1.67  tff(c_1031, plain, (r2_hidden('#skF_1'('#skF_6', k1_tarski('#skF_5')), k1_tarski('#skF_5')) | r1_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_1014])).
% 3.73/1.67  tff(c_1035, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_1031])).
% 3.73/1.67  tff(c_373, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, k3_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.73/1.67  tff(c_404, plain, (![B_99, A_100, C_101]: (~r1_xboole_0(B_99, A_100) | ~r2_hidden(C_101, k3_xboole_0(A_100, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_373])).
% 3.73/1.67  tff(c_415, plain, (![B_99, A_100]: (~r1_xboole_0(B_99, A_100) | k3_xboole_0(A_100, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_404])).
% 3.73/1.67  tff(c_1045, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_1035, c_415])).
% 3.73/1.67  tff(c_116, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.73/1.67  tff(c_128, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_116])).
% 3.73/1.67  tff(c_1071, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1045, c_128])).
% 3.73/1.67  tff(c_1104, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1071])).
% 3.73/1.67  tff(c_42, plain, (![B_47, A_46]: (~r2_hidden(B_47, A_46) | k4_xboole_0(A_46, k1_tarski(B_47))!=A_46)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.73/1.67  tff(c_1207, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1104, c_42])).
% 3.73/1.67  tff(c_1225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_367, c_1207])).
% 3.73/1.67  tff(c_1227, plain, (~r1_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_1031])).
% 3.73/1.67  tff(c_1226, plain, (r2_hidden('#skF_1'('#skF_6', k1_tarski('#skF_5')), k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_1031])).
% 3.73/1.67  tff(c_634, plain, (![A_123, C_124, B_125]: (~r2_hidden(A_123, C_124) | ~r2_hidden(A_123, B_125) | ~r2_hidden(A_123, k5_xboole_0(B_125, C_124)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.73/1.67  tff(c_1240, plain, (![A_177, A_178, B_179]: (~r2_hidden(A_177, k3_xboole_0(A_178, B_179)) | ~r2_hidden(A_177, A_178) | ~r2_hidden(A_177, k4_xboole_0(A_178, B_179)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_634])).
% 3.73/1.67  tff(c_1255, plain, (![A_177]: (~r2_hidden(A_177, k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')) | ~r2_hidden(A_177, k1_tarski('#skF_5')) | ~r2_hidden(A_177, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_543, c_1240])).
% 3.73/1.67  tff(c_1288, plain, (![A_180]: (~r2_hidden(A_180, k3_xboole_0('#skF_6', k1_tarski('#skF_5'))) | ~r2_hidden(A_180, k1_tarski('#skF_5')) | ~r2_hidden(A_180, k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1255])).
% 3.73/1.67  tff(c_1296, plain, (~r2_hidden('#skF_1'('#skF_6', k1_tarski('#skF_5')), k1_tarski('#skF_5')) | r1_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_1288])).
% 3.73/1.67  tff(c_1307, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1226, c_1296])).
% 3.73/1.67  tff(c_1309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1227, c_1307])).
% 3.73/1.67  tff(c_1310, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 3.73/1.67  tff(c_1311, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 3.73/1.67  tff(c_52, plain, (~r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.73/1.67  tff(c_1508, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1311, c_52])).
% 3.73/1.67  tff(c_1643, plain, (![A_231, C_232, B_233]: (~r2_hidden(A_231, C_232) | ~r2_hidden(A_231, B_233) | ~r2_hidden(A_231, k5_xboole_0(B_233, C_232)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.73/1.67  tff(c_1729, plain, (![A_254, A_255, B_256]: (~r2_hidden(A_254, k3_xboole_0(A_255, B_256)) | ~r2_hidden(A_254, A_255) | ~r2_hidden(A_254, k4_xboole_0(A_255, B_256)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1643])).
% 3.73/1.67  tff(c_1738, plain, (![A_254]: (~r2_hidden(A_254, k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')) | ~r2_hidden(A_254, k1_tarski('#skF_5')) | ~r2_hidden(A_254, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1508, c_1729])).
% 3.73/1.67  tff(c_1788, plain, (![A_263]: (~r2_hidden(A_263, k3_xboole_0('#skF_6', k1_tarski('#skF_5'))) | ~r2_hidden(A_263, k1_tarski('#skF_5')) | ~r2_hidden(A_263, k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1738])).
% 3.73/1.67  tff(c_1805, plain, (~r2_hidden('#skF_1'('#skF_6', k1_tarski('#skF_5')), k1_tarski('#skF_5')) | r1_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_1788])).
% 3.73/1.67  tff(c_1809, plain, (~r2_hidden('#skF_1'('#skF_6', k1_tarski('#skF_5')), k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_1805])).
% 3.73/1.67  tff(c_1322, plain, (![A_185, B_186]: (k5_xboole_0(A_185, k3_xboole_0(A_185, B_186))=k4_xboole_0(A_185, B_186))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.73/1.67  tff(c_1334, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1322])).
% 3.73/1.67  tff(c_1682, plain, (![A_237, B_238, C_239]: (r2_hidden(A_237, B_238) | ~r2_hidden(A_237, C_239) | r2_hidden(A_237, k5_xboole_0(B_238, C_239)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.73/1.67  tff(c_1810, plain, (![A_264, B_265, A_266]: (r2_hidden(A_264, B_265) | ~r2_hidden(A_264, k3_xboole_0(A_266, B_265)) | r2_hidden(A_264, k4_xboole_0(B_265, A_266)))), inference(superposition, [status(thm), theory('equality')], [c_1334, c_1682])).
% 3.73/1.67  tff(c_1917, plain, (![A_283]: (r2_hidden(A_283, k1_tarski('#skF_5')) | ~r2_hidden(A_283, k3_xboole_0('#skF_6', k1_tarski('#skF_5'))) | r2_hidden(A_283, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1508, c_1810])).
% 3.73/1.67  tff(c_1925, plain, (r2_hidden('#skF_1'('#skF_6', k1_tarski('#skF_5')), k1_tarski('#skF_5')) | r1_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_1917])).
% 3.73/1.67  tff(c_1938, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1809, c_1809, c_1925])).
% 3.73/1.67  tff(c_1337, plain, (![A_187, B_188, C_189]: (~r1_xboole_0(A_187, B_188) | ~r2_hidden(C_189, k3_xboole_0(A_187, B_188)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.73/1.67  tff(c_1348, plain, (![A_187, B_188]: (~r1_xboole_0(A_187, B_188) | k3_xboole_0(A_187, B_188)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_1337])).
% 3.73/1.67  tff(c_1963, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1938, c_1348])).
% 3.73/1.67  tff(c_1988, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1963, c_22])).
% 3.73/1.67  tff(c_2005, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1988])).
% 3.73/1.67  tff(c_2233, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2005, c_42])).
% 3.73/1.67  tff(c_2256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1310, c_2233])).
% 3.73/1.67  tff(c_2257, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_1805])).
% 3.73/1.67  tff(c_2291, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2257, c_1348])).
% 3.73/1.67  tff(c_2382, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2291, c_22])).
% 3.73/1.67  tff(c_2399, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2382])).
% 3.73/1.67  tff(c_2435, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2399, c_42])).
% 3.73/1.67  tff(c_2452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1310, c_2435])).
% 3.73/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.67  
% 3.73/1.67  Inference rules
% 3.73/1.67  ----------------------
% 3.73/1.67  #Ref     : 0
% 3.73/1.67  #Sup     : 566
% 3.73/1.67  #Fact    : 2
% 3.73/1.67  #Define  : 0
% 3.73/1.67  #Split   : 9
% 3.73/1.67  #Chain   : 0
% 3.73/1.67  #Close   : 0
% 3.73/1.67  
% 3.73/1.67  Ordering : KBO
% 3.73/1.67  
% 3.73/1.67  Simplification rules
% 3.73/1.67  ----------------------
% 3.73/1.67  #Subsume      : 126
% 3.73/1.67  #Demod        : 194
% 3.73/1.67  #Tautology    : 281
% 3.73/1.67  #SimpNegUnit  : 47
% 3.73/1.67  #BackRed      : 6
% 3.73/1.67  
% 3.73/1.67  #Partial instantiations: 0
% 3.73/1.67  #Strategies tried      : 1
% 3.73/1.67  
% 3.73/1.67  Timing (in seconds)
% 3.73/1.67  ----------------------
% 3.73/1.67  Preprocessing        : 0.31
% 3.73/1.67  Parsing              : 0.15
% 3.73/1.67  CNF conversion       : 0.02
% 3.73/1.67  Main loop            : 0.55
% 3.73/1.67  Inferencing          : 0.21
% 3.73/1.67  Reduction            : 0.18
% 3.73/1.67  Demodulation         : 0.12
% 3.73/1.67  BG Simplification    : 0.03
% 3.73/1.67  Subsumption          : 0.10
% 3.73/1.67  Abstraction          : 0.03
% 3.73/1.67  MUC search           : 0.00
% 3.73/1.67  Cooper               : 0.00
% 3.73/1.67  Total                : 0.90
% 3.73/1.68  Index Insertion      : 0.00
% 3.73/1.68  Index Deletion       : 0.00
% 3.73/1.68  Index Matching       : 0.00
% 3.73/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
