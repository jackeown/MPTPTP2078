%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:12 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 259 expanded)
%              Number of leaves         :   42 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 472 expanded)
%              Number of equality atoms :   59 ( 295 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_115,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_90,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_82,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_72,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_105,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_104,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_1322,plain,(
    ! [B_153,A_154] :
      ( k3_xboole_0(B_153,k1_tarski(A_154)) = k1_tarski(A_154)
      | ~ r2_hidden(A_154,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_76,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_100,plain,(
    ! [A_77,B_78] : r1_tarski(A_77,k2_xboole_0(A_77,B_78)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_103,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_100])).

tff(c_316,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_336,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_103,c_316])).

tff(c_1351,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_336])).

tff(c_1385,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1351])).

tff(c_64,plain,(
    ! [A_65,B_66] :
      ( r1_xboole_0(k1_tarski(A_65),B_66)
      | r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_531,plain,(
    ! [A_111,B_112,C_113] :
      ( ~ r1_xboole_0(A_111,B_112)
      | ~ r2_hidden(C_113,k3_xboole_0(A_111,B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_540,plain,(
    ! [C_113] :
      ( ~ r1_xboole_0('#skF_4',k1_tarski('#skF_3'))
      | ~ r2_hidden(C_113,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_531])).

tff(c_589,plain,(
    ~ r1_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_1531,plain,(
    ! [A_159,B_160] :
      ( r2_hidden('#skF_2'(A_159,B_160),k3_xboole_0(A_159,B_160))
      | r1_xboole_0(A_159,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1558,plain,
    ( r2_hidden('#skF_2'('#skF_4',k1_tarski('#skF_3')),'#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_1531])).

tff(c_1569,plain,(
    r2_hidden('#skF_2'('#skF_4',k1_tarski('#skF_3')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_1558])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1687,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1569,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1125,plain,(
    ! [A_144,B_145] :
      ( ~ r1_xboole_0(A_144,B_145)
      | v1_xboole_0(k3_xboole_0(A_144,B_145)) ) ),
    inference(resolution,[status(thm)],[c_6,c_531])).

tff(c_1932,plain,(
    ! [A_183,B_184] :
      ( ~ r1_xboole_0(A_183,B_184)
      | v1_xboole_0(k3_xboole_0(B_184,A_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1125])).

tff(c_1959,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_1932])).

tff(c_1970,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1687,c_1959])).

tff(c_1979,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1970])).

tff(c_1985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1385,c_1979])).

tff(c_1993,plain,(
    ! [C_185] : ~ r2_hidden(C_185,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_1998,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_1993])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2001,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1998,c_8])).

tff(c_2005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_2001])).

tff(c_2006,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_48,plain,(
    ! [A_35,B_36] : r1_tarski(A_35,k2_xboole_0(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2007,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2196,plain,(
    ! [A_204,B_205] :
      ( k4_xboole_0(A_204,B_205) = '#skF_4'
      | ~ r1_tarski(A_204,B_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2007,c_28])).

tff(c_2311,plain,(
    ! [A_216,B_217] : k4_xboole_0(A_216,k2_xboole_0(A_216,B_217)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_2196])).

tff(c_42,plain,(
    ! [A_31,B_32] : r1_tarski(k4_xboole_0(A_31,B_32),A_31) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2324,plain,(
    ! [A_216] : r1_tarski('#skF_4',A_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_2311,c_42])).

tff(c_2443,plain,(
    ! [A_224,B_225] :
      ( k2_xboole_0(A_224,B_225) = B_225
      | ~ r1_tarski(A_224,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2460,plain,(
    ! [A_216] : k2_xboole_0('#skF_4',A_216) = A_216 ),
    inference(resolution,[status(thm)],[c_2324,c_2443])).

tff(c_2600,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2460,c_76])).

tff(c_2602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2006,c_2600])).

tff(c_2603,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2604,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2734,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2604,c_2604,c_74])).

tff(c_3259,plain,(
    ! [A_269,B_270] :
      ( r1_xboole_0(k1_tarski(A_269),B_270)
      | r2_hidden(A_269,B_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3262,plain,(
    ! [B_270] :
      ( r1_xboole_0('#skF_4',B_270)
      | r2_hidden('#skF_3',B_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2604,c_3259])).

tff(c_3720,plain,(
    ! [B_295,A_296] :
      ( k3_xboole_0(B_295,k1_tarski(A_296)) = k1_tarski(A_296)
      | ~ r2_hidden(A_296,B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3771,plain,(
    ! [B_295] :
      ( k3_xboole_0(B_295,'#skF_4') = k1_tarski('#skF_3')
      | ~ r2_hidden('#skF_3',B_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2604,c_3720])).

tff(c_3901,plain,(
    ! [B_301] :
      ( k3_xboole_0(B_301,'#skF_4') = '#skF_4'
      | ~ r2_hidden('#skF_3',B_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2604,c_3771])).

tff(c_3905,plain,(
    ! [B_270] :
      ( k3_xboole_0(B_270,'#skF_4') = '#skF_4'
      | r1_xboole_0('#skF_4',B_270) ) ),
    inference(resolution,[status(thm)],[c_3262,c_3901])).

tff(c_46,plain,(
    ! [A_34] : k5_xboole_0(A_34,k1_xboole_0) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    ! [A_30] : k3_xboole_0(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3366,plain,(
    ! [A_280,B_281] : k5_xboole_0(A_280,k3_xboole_0(A_280,B_281)) = k4_xboole_0(A_280,B_281) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3396,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = k4_xboole_0(A_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3366])).

tff(c_3406,plain,(
    ! [A_282] : k4_xboole_0(A_282,k1_xboole_0) = A_282 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3396])).

tff(c_3426,plain,(
    ! [A_282] : r1_tarski(A_282,A_282) ),
    inference(superposition,[status(thm),theory(equality)],[c_3406,c_42])).

tff(c_2606,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2604,c_76])).

tff(c_3649,plain,(
    ! [A_291,C_292,B_293] :
      ( r1_tarski(A_291,k2_xboole_0(C_292,B_293))
      | ~ r1_tarski(A_291,B_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3677,plain,(
    ! [A_294] :
      ( r1_tarski(A_294,'#skF_4')
      | ~ r1_tarski(A_294,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2606,c_3649])).

tff(c_3698,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3426,c_3677])).

tff(c_38,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3713,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3698,c_38])).

tff(c_3863,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3713])).

tff(c_24,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,k3_xboole_0(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3880,plain,(
    ! [C_15] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_15,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3863,c_24])).

tff(c_4151,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3880])).

tff(c_4158,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3905,c_4151])).

tff(c_4160,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4158,c_3713])).

tff(c_4162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2734,c_4160])).

tff(c_4165,plain,(
    ! [C_317] : ~ r2_hidden(C_317,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3880])).

tff(c_4175,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_4165])).

tff(c_4206,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4175,c_8])).

tff(c_4210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2603,c_4206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.80  
% 4.35/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.35/1.81  
% 4.35/1.81  %Foreground sorts:
% 4.35/1.81  
% 4.35/1.81  
% 4.35/1.81  %Background operators:
% 4.35/1.81  
% 4.35/1.81  
% 4.35/1.81  %Foreground operators:
% 4.35/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.35/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.35/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.35/1.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.35/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.35/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.35/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.35/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.35/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.35/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.35/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.35/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.35/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.35/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.35/1.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.35/1.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.35/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.35/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.35/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.35/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.35/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.35/1.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.35/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.35/1.81  
% 4.35/1.82  tff(f_136, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.35/1.82  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.35/1.82  tff(f_115, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 4.35/1.82  tff(f_92, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.35/1.82  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.35/1.82  tff(f_111, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.35/1.82  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.35/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.35/1.82  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.35/1.82  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.35/1.82  tff(f_84, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.35/1.82  tff(f_76, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.35/1.82  tff(f_90, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.35/1.82  tff(f_82, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.35/1.82  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.35/1.82  tff(f_72, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.35/1.82  tff(c_72, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.35/1.82  tff(c_105, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_72])).
% 4.35/1.82  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.35/1.82  tff(c_70, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.35/1.82  tff(c_104, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_70])).
% 4.35/1.82  tff(c_1322, plain, (![B_153, A_154]: (k3_xboole_0(B_153, k1_tarski(A_154))=k1_tarski(A_154) | ~r2_hidden(A_154, B_153))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.35/1.82  tff(c_76, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.35/1.82  tff(c_100, plain, (![A_77, B_78]: (r1_tarski(A_77, k2_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.35/1.82  tff(c_103, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_100])).
% 4.35/1.82  tff(c_316, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.35/1.82  tff(c_336, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(resolution, [status(thm)], [c_103, c_316])).
% 4.35/1.82  tff(c_1351, plain, (k1_tarski('#skF_3')='#skF_4' | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1322, c_336])).
% 4.35/1.82  tff(c_1385, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_104, c_1351])).
% 4.35/1.82  tff(c_64, plain, (![A_65, B_66]: (r1_xboole_0(k1_tarski(A_65), B_66) | r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.35/1.82  tff(c_531, plain, (![A_111, B_112, C_113]: (~r1_xboole_0(A_111, B_112) | ~r2_hidden(C_113, k3_xboole_0(A_111, B_112)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.35/1.82  tff(c_540, plain, (![C_113]: (~r1_xboole_0('#skF_4', k1_tarski('#skF_3')) | ~r2_hidden(C_113, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_336, c_531])).
% 4.35/1.82  tff(c_589, plain, (~r1_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_540])).
% 4.35/1.82  tff(c_1531, plain, (![A_159, B_160]: (r2_hidden('#skF_2'(A_159, B_160), k3_xboole_0(A_159, B_160)) | r1_xboole_0(A_159, B_160))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.35/1.82  tff(c_1558, plain, (r2_hidden('#skF_2'('#skF_4', k1_tarski('#skF_3')), '#skF_4') | r1_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_336, c_1531])).
% 4.35/1.82  tff(c_1569, plain, (r2_hidden('#skF_2'('#skF_4', k1_tarski('#skF_3')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_589, c_1558])).
% 4.35/1.82  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.35/1.82  tff(c_1687, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1569, c_4])).
% 4.35/1.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.35/1.82  tff(c_1125, plain, (![A_144, B_145]: (~r1_xboole_0(A_144, B_145) | v1_xboole_0(k3_xboole_0(A_144, B_145)))), inference(resolution, [status(thm)], [c_6, c_531])).
% 4.35/1.82  tff(c_1932, plain, (![A_183, B_184]: (~r1_xboole_0(A_183, B_184) | v1_xboole_0(k3_xboole_0(B_184, A_183)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1125])).
% 4.35/1.82  tff(c_1959, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_336, c_1932])).
% 4.35/1.82  tff(c_1970, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1687, c_1959])).
% 4.35/1.82  tff(c_1979, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_1970])).
% 4.35/1.82  tff(c_1985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1385, c_1979])).
% 4.35/1.82  tff(c_1993, plain, (![C_185]: (~r2_hidden(C_185, '#skF_4'))), inference(splitRight, [status(thm)], [c_540])).
% 4.35/1.82  tff(c_1998, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_6, c_1993])).
% 4.35/1.82  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.35/1.82  tff(c_2001, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1998, c_8])).
% 4.35/1.82  tff(c_2005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_2001])).
% 4.35/1.82  tff(c_2006, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_72])).
% 4.35/1.82  tff(c_48, plain, (![A_35, B_36]: (r1_tarski(A_35, k2_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.35/1.82  tff(c_2007, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_72])).
% 4.35/1.82  tff(c_28, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.35/1.82  tff(c_2196, plain, (![A_204, B_205]: (k4_xboole_0(A_204, B_205)='#skF_4' | ~r1_tarski(A_204, B_205))), inference(demodulation, [status(thm), theory('equality')], [c_2007, c_28])).
% 4.35/1.82  tff(c_2311, plain, (![A_216, B_217]: (k4_xboole_0(A_216, k2_xboole_0(A_216, B_217))='#skF_4')), inference(resolution, [status(thm)], [c_48, c_2196])).
% 4.35/1.82  tff(c_42, plain, (![A_31, B_32]: (r1_tarski(k4_xboole_0(A_31, B_32), A_31))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.35/1.82  tff(c_2324, plain, (![A_216]: (r1_tarski('#skF_4', A_216))), inference(superposition, [status(thm), theory('equality')], [c_2311, c_42])).
% 4.35/1.82  tff(c_2443, plain, (![A_224, B_225]: (k2_xboole_0(A_224, B_225)=B_225 | ~r1_tarski(A_224, B_225))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.35/1.82  tff(c_2460, plain, (![A_216]: (k2_xboole_0('#skF_4', A_216)=A_216)), inference(resolution, [status(thm)], [c_2324, c_2443])).
% 4.35/1.82  tff(c_2600, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2460, c_76])).
% 4.35/1.82  tff(c_2602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2006, c_2600])).
% 4.35/1.82  tff(c_2603, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_70])).
% 4.35/1.82  tff(c_2604, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_70])).
% 4.35/1.82  tff(c_74, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.35/1.82  tff(c_2734, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2604, c_2604, c_74])).
% 4.35/1.82  tff(c_3259, plain, (![A_269, B_270]: (r1_xboole_0(k1_tarski(A_269), B_270) | r2_hidden(A_269, B_270))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.35/1.82  tff(c_3262, plain, (![B_270]: (r1_xboole_0('#skF_4', B_270) | r2_hidden('#skF_3', B_270))), inference(superposition, [status(thm), theory('equality')], [c_2604, c_3259])).
% 4.35/1.82  tff(c_3720, plain, (![B_295, A_296]: (k3_xboole_0(B_295, k1_tarski(A_296))=k1_tarski(A_296) | ~r2_hidden(A_296, B_295))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.35/1.82  tff(c_3771, plain, (![B_295]: (k3_xboole_0(B_295, '#skF_4')=k1_tarski('#skF_3') | ~r2_hidden('#skF_3', B_295))), inference(superposition, [status(thm), theory('equality')], [c_2604, c_3720])).
% 4.35/1.82  tff(c_3901, plain, (![B_301]: (k3_xboole_0(B_301, '#skF_4')='#skF_4' | ~r2_hidden('#skF_3', B_301))), inference(demodulation, [status(thm), theory('equality')], [c_2604, c_3771])).
% 4.35/1.82  tff(c_3905, plain, (![B_270]: (k3_xboole_0(B_270, '#skF_4')='#skF_4' | r1_xboole_0('#skF_4', B_270))), inference(resolution, [status(thm)], [c_3262, c_3901])).
% 4.35/1.82  tff(c_46, plain, (![A_34]: (k5_xboole_0(A_34, k1_xboole_0)=A_34)), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.35/1.82  tff(c_40, plain, (![A_30]: (k3_xboole_0(A_30, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.35/1.82  tff(c_3366, plain, (![A_280, B_281]: (k5_xboole_0(A_280, k3_xboole_0(A_280, B_281))=k4_xboole_0(A_280, B_281))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.35/1.82  tff(c_3396, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=k4_xboole_0(A_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_3366])).
% 4.35/1.82  tff(c_3406, plain, (![A_282]: (k4_xboole_0(A_282, k1_xboole_0)=A_282)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3396])).
% 4.35/1.82  tff(c_3426, plain, (![A_282]: (r1_tarski(A_282, A_282))), inference(superposition, [status(thm), theory('equality')], [c_3406, c_42])).
% 4.35/1.82  tff(c_2606, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2604, c_76])).
% 4.35/1.82  tff(c_3649, plain, (![A_291, C_292, B_293]: (r1_tarski(A_291, k2_xboole_0(C_292, B_293)) | ~r1_tarski(A_291, B_293))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.35/1.82  tff(c_3677, plain, (![A_294]: (r1_tarski(A_294, '#skF_4') | ~r1_tarski(A_294, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2606, c_3649])).
% 4.35/1.82  tff(c_3698, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3426, c_3677])).
% 4.35/1.82  tff(c_38, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.35/1.82  tff(c_3713, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_3698, c_38])).
% 4.35/1.82  tff(c_3863, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2, c_3713])).
% 4.35/1.82  tff(c_24, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, k3_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.35/1.82  tff(c_3880, plain, (![C_15]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_15, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3863, c_24])).
% 4.35/1.82  tff(c_4151, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_3880])).
% 4.35/1.82  tff(c_4158, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_3905, c_4151])).
% 4.35/1.82  tff(c_4160, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4158, c_3713])).
% 4.35/1.82  tff(c_4162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2734, c_4160])).
% 4.35/1.82  tff(c_4165, plain, (![C_317]: (~r2_hidden(C_317, '#skF_5'))), inference(splitRight, [status(thm)], [c_3880])).
% 4.35/1.82  tff(c_4175, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6, c_4165])).
% 4.35/1.82  tff(c_4206, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4175, c_8])).
% 4.35/1.82  tff(c_4210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2603, c_4206])).
% 4.35/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.82  
% 4.35/1.82  Inference rules
% 4.35/1.82  ----------------------
% 4.35/1.82  #Ref     : 0
% 4.35/1.82  #Sup     : 1005
% 4.35/1.82  #Fact    : 0
% 4.35/1.82  #Define  : 0
% 4.35/1.82  #Split   : 9
% 4.35/1.82  #Chain   : 0
% 4.35/1.82  #Close   : 0
% 4.35/1.82  
% 4.35/1.82  Ordering : KBO
% 4.35/1.82  
% 4.35/1.82  Simplification rules
% 4.35/1.82  ----------------------
% 4.35/1.82  #Subsume      : 67
% 4.35/1.82  #Demod        : 343
% 4.35/1.82  #Tautology    : 688
% 4.35/1.82  #SimpNegUnit  : 30
% 4.35/1.82  #BackRed      : 21
% 4.35/1.82  
% 4.35/1.82  #Partial instantiations: 0
% 4.35/1.82  #Strategies tried      : 1
% 4.35/1.82  
% 4.35/1.82  Timing (in seconds)
% 4.35/1.82  ----------------------
% 4.56/1.83  Preprocessing        : 0.35
% 4.56/1.83  Parsing              : 0.18
% 4.56/1.83  CNF conversion       : 0.03
% 4.56/1.83  Main loop            : 0.72
% 4.56/1.83  Inferencing          : 0.25
% 4.56/1.83  Reduction            : 0.26
% 4.56/1.83  Demodulation         : 0.19
% 4.56/1.83  BG Simplification    : 0.03
% 4.56/1.83  Subsumption          : 0.11
% 4.56/1.83  Abstraction          : 0.03
% 4.56/1.83  MUC search           : 0.00
% 4.56/1.83  Cooper               : 0.00
% 4.56/1.83  Total                : 1.10
% 4.56/1.83  Index Insertion      : 0.00
% 4.56/1.83  Index Deletion       : 0.00
% 4.56/1.83  Index Matching       : 0.00
% 4.56/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
