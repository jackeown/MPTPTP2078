%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:46 EST 2020

% Result     : Theorem 8.44s
% Output     : CNFRefutation 8.44s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 434 expanded)
%              Number of leaves         :   39 ( 162 expanded)
%              Depth                    :   15
%              Number of atoms          :  116 ( 665 expanded)
%              Number of equality atoms :   47 ( 321 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_86,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_92,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_90,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_62,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_130,plain,(
    ! [B_77,A_78] : k5_xboole_0(B_77,A_78) = k5_xboole_0(A_78,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [A_28] : k5_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_146,plain,(
    ! [A_78] : k5_xboole_0(k1_xboole_0,A_78) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_32])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_22,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_4'(A_20),A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2102,plain,(
    ! [A_201,B_202,C_203,D_204] :
      ( r2_hidden(k4_tarski(A_201,B_202),k2_zfmisc_1(C_203,D_204))
      | ~ r2_hidden(B_202,D_204)
      | ~ r2_hidden(A_201,C_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2344,plain,(
    ! [A_216,B_217] :
      ( r2_hidden(k4_tarski(A_216,B_217),k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(B_217,'#skF_6')
      | ~ r2_hidden(A_216,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2102])).

tff(c_60,plain,(
    ! [A_66,C_68,B_67,D_69] :
      ( r2_hidden(A_66,C_68)
      | ~ r2_hidden(k4_tarski(A_66,B_67),k2_zfmisc_1(C_68,D_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2361,plain,(
    ! [A_216,B_217] :
      ( r2_hidden(A_216,'#skF_6')
      | ~ r2_hidden(B_217,'#skF_6')
      | ~ r2_hidden(A_216,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2344,c_60])).

tff(c_2383,plain,(
    ! [B_224] : ~ r2_hidden(B_224,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2361])).

tff(c_2399,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_22,c_2383])).

tff(c_2406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2399])).

tff(c_2408,plain,(
    ! [A_225] :
      ( r2_hidden(A_225,'#skF_6')
      | ~ r2_hidden(A_225,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_2361])).

tff(c_6562,plain,(
    ! [B_317] :
      ( r2_hidden('#skF_1'('#skF_5',B_317),'#skF_6')
      | r1_tarski('#skF_5',B_317) ) ),
    inference(resolution,[status(thm)],[c_10,c_2408])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6570,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_6562,c_8])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6578,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6570,c_26])).

tff(c_30,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    ! [A_34] : k5_xboole_0(A_34,A_34) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1458,plain,(
    ! [A_182,B_183,C_184] : k5_xboole_0(k5_xboole_0(A_182,B_183),C_184) = k5_xboole_0(A_182,k5_xboole_0(B_183,C_184)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1559,plain,(
    ! [A_34,C_184] : k5_xboole_0(A_34,k5_xboole_0(A_34,C_184)) = k5_xboole_0(k1_xboole_0,C_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1458])).

tff(c_1573,plain,(
    ! [A_185,C_186] : k5_xboole_0(A_185,k5_xboole_0(A_185,C_186)) = C_186 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_1559])).

tff(c_1624,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1573])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4070,plain,(
    ! [C_287,A_288,B_289] : k5_xboole_0(C_287,k5_xboole_0(A_288,B_289)) = k5_xboole_0(A_288,k5_xboole_0(B_289,C_287)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1458,c_4])).

tff(c_4480,plain,(
    ! [A_290,C_291] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_290,C_291)) = k5_xboole_0(C_291,A_290) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_4070])).

tff(c_4580,plain,(
    ! [A_26,B_27] : k5_xboole_0(k4_xboole_0(A_26,B_27),A_26) = k5_xboole_0(k1_xboole_0,k3_xboole_0(A_26,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1624,c_4480])).

tff(c_4658,plain,(
    ! [A_26,B_27] : k5_xboole_0(k4_xboole_0(A_26,B_27),A_26) = k3_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_4580])).

tff(c_6585,plain,(
    k5_xboole_0(k1_xboole_0,'#skF_5') = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6578,c_4658])).

tff(c_6621,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_146,c_6585])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2424,plain,
    ( r2_hidden('#skF_4'('#skF_5'),'#skF_6')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_2408])).

tff(c_2430,plain,(
    r2_hidden('#skF_4'('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2424])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2446,plain,(
    ! [B_233] :
      ( r2_hidden('#skF_4'('#skF_5'),B_233)
      | ~ r1_tarski('#skF_6',B_233) ) ),
    inference(resolution,[status(thm)],[c_2430,c_6])).

tff(c_343,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r1_xboole_0(A_99,B_100)
      | ~ r2_hidden(C_101,k3_xboole_0(A_99,B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_349,plain,(
    ! [B_2,A_1,C_101] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_101,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_343])).

tff(c_2467,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r1_tarski('#skF_6',k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_2446,c_349])).

tff(c_6647,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6621,c_2467])).

tff(c_7295,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6647])).

tff(c_1219,plain,(
    ! [A_166,C_167,B_168,D_169] :
      ( r2_hidden(A_166,C_167)
      | ~ r2_hidden(k4_tarski(A_166,B_168),k2_zfmisc_1(C_167,D_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1222,plain,(
    ! [A_166,B_168] :
      ( r2_hidden(A_166,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_166,B_168),k2_zfmisc_1('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1219])).

tff(c_2122,plain,(
    ! [A_201,B_202] :
      ( r2_hidden(A_201,'#skF_5')
      | ~ r2_hidden(B_202,'#skF_5')
      | ~ r2_hidden(A_201,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2102,c_1222])).

tff(c_2478,plain,(
    ! [B_234] : ~ r2_hidden(B_234,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2122])).

tff(c_2498,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_2478])).

tff(c_2506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2498])).

tff(c_2508,plain,(
    ! [A_235] :
      ( r2_hidden(A_235,'#skF_5')
      | ~ r2_hidden(A_235,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_2122])).

tff(c_15218,plain,(
    ! [A_451] :
      ( r1_tarski(A_451,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_451,'#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2508,c_8])).

tff(c_15230,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_15218])).

tff(c_15237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7295,c_7295,c_15230])).

tff(c_15239,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_6647])).

tff(c_15248,plain,(
    k4_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15239,c_26])).

tff(c_574,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k3_xboole_0(A_114,B_115)) = k4_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_606,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_574])).

tff(c_4673,plain,(
    ! [B_292,A_293] : k5_xboole_0(B_292,k4_xboole_0(B_292,A_293)) = k3_xboole_0(A_293,B_292) ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_1573])).

tff(c_1637,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1573])).

tff(c_4712,plain,(
    ! [B_292,A_293] : k5_xboole_0(k4_xboole_0(B_292,A_293),k3_xboole_0(A_293,B_292)) = B_292 ),
    inference(superposition,[status(thm),theory(equality)],[c_4673,c_1637])).

tff(c_15260,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0('#skF_5','#skF_6')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_15248,c_4712])).

tff(c_15299,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_6621,c_2,c_15260])).

tff(c_15301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_15299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.44/3.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.44/3.34  
% 8.44/3.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.44/3.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 8.44/3.35  
% 8.44/3.35  %Foreground sorts:
% 8.44/3.35  
% 8.44/3.35  
% 8.44/3.35  %Background operators:
% 8.44/3.35  
% 8.44/3.35  
% 8.44/3.35  %Foreground operators:
% 8.44/3.35  tff('#skF_4', type, '#skF_4': $i > $i).
% 8.44/3.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.44/3.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.44/3.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.44/3.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.44/3.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.44/3.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.44/3.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.44/3.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.44/3.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.44/3.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.44/3.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.44/3.35  tff('#skF_5', type, '#skF_5': $i).
% 8.44/3.35  tff('#skF_6', type, '#skF_6': $i).
% 8.44/3.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.44/3.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.44/3.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.44/3.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.44/3.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.44/3.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.44/3.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.44/3.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.44/3.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.44/3.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.44/3.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.44/3.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.44/3.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.44/3.35  
% 8.44/3.36  tff(f_123, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 8.44/3.36  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.44/3.36  tff(f_86, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.44/3.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.44/3.36  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.44/3.36  tff(f_76, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.44/3.36  tff(f_114, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 8.44/3.36  tff(f_80, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.44/3.36  tff(f_84, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.44/3.36  tff(f_92, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.44/3.36  tff(f_90, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.44/3.36  tff(f_68, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.44/3.36  tff(c_62, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.44/3.36  tff(c_130, plain, (![B_77, A_78]: (k5_xboole_0(B_77, A_78)=k5_xboole_0(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.44/3.36  tff(c_32, plain, (![A_28]: (k5_xboole_0(A_28, k1_xboole_0)=A_28)), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.44/3.36  tff(c_146, plain, (![A_78]: (k5_xboole_0(k1_xboole_0, A_78)=A_78)), inference(superposition, [status(thm), theory('equality')], [c_130, c_32])).
% 8.44/3.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.44/3.36  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.44/3.36  tff(c_64, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.44/3.36  tff(c_22, plain, (![A_20]: (r2_hidden('#skF_4'(A_20), A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.44/3.36  tff(c_68, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.44/3.36  tff(c_2102, plain, (![A_201, B_202, C_203, D_204]: (r2_hidden(k4_tarski(A_201, B_202), k2_zfmisc_1(C_203, D_204)) | ~r2_hidden(B_202, D_204) | ~r2_hidden(A_201, C_203))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.44/3.36  tff(c_2344, plain, (![A_216, B_217]: (r2_hidden(k4_tarski(A_216, B_217), k2_zfmisc_1('#skF_6', '#skF_5')) | ~r2_hidden(B_217, '#skF_6') | ~r2_hidden(A_216, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2102])).
% 8.44/3.36  tff(c_60, plain, (![A_66, C_68, B_67, D_69]: (r2_hidden(A_66, C_68) | ~r2_hidden(k4_tarski(A_66, B_67), k2_zfmisc_1(C_68, D_69)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.44/3.36  tff(c_2361, plain, (![A_216, B_217]: (r2_hidden(A_216, '#skF_6') | ~r2_hidden(B_217, '#skF_6') | ~r2_hidden(A_216, '#skF_5'))), inference(resolution, [status(thm)], [c_2344, c_60])).
% 8.44/3.36  tff(c_2383, plain, (![B_224]: (~r2_hidden(B_224, '#skF_6'))), inference(splitLeft, [status(thm)], [c_2361])).
% 8.44/3.36  tff(c_2399, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_22, c_2383])).
% 8.44/3.36  tff(c_2406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2399])).
% 8.44/3.36  tff(c_2408, plain, (![A_225]: (r2_hidden(A_225, '#skF_6') | ~r2_hidden(A_225, '#skF_5'))), inference(splitRight, [status(thm)], [c_2361])).
% 8.44/3.36  tff(c_6562, plain, (![B_317]: (r2_hidden('#skF_1'('#skF_5', B_317), '#skF_6') | r1_tarski('#skF_5', B_317))), inference(resolution, [status(thm)], [c_10, c_2408])).
% 8.44/3.36  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.44/3.36  tff(c_6570, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_6562, c_8])).
% 8.44/3.36  tff(c_26, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.44/3.36  tff(c_6578, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_6570, c_26])).
% 8.44/3.36  tff(c_30, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.44/3.36  tff(c_38, plain, (![A_34]: (k5_xboole_0(A_34, A_34)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.44/3.36  tff(c_1458, plain, (![A_182, B_183, C_184]: (k5_xboole_0(k5_xboole_0(A_182, B_183), C_184)=k5_xboole_0(A_182, k5_xboole_0(B_183, C_184)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.44/3.36  tff(c_1559, plain, (![A_34, C_184]: (k5_xboole_0(A_34, k5_xboole_0(A_34, C_184))=k5_xboole_0(k1_xboole_0, C_184))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1458])).
% 8.44/3.36  tff(c_1573, plain, (![A_185, C_186]: (k5_xboole_0(A_185, k5_xboole_0(A_185, C_186))=C_186)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_1559])).
% 8.44/3.36  tff(c_1624, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1573])).
% 8.44/3.36  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.44/3.36  tff(c_4070, plain, (![C_287, A_288, B_289]: (k5_xboole_0(C_287, k5_xboole_0(A_288, B_289))=k5_xboole_0(A_288, k5_xboole_0(B_289, C_287)))), inference(superposition, [status(thm), theory('equality')], [c_1458, c_4])).
% 8.44/3.36  tff(c_4480, plain, (![A_290, C_291]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_290, C_291))=k5_xboole_0(C_291, A_290))), inference(superposition, [status(thm), theory('equality')], [c_146, c_4070])).
% 8.44/3.36  tff(c_4580, plain, (![A_26, B_27]: (k5_xboole_0(k4_xboole_0(A_26, B_27), A_26)=k5_xboole_0(k1_xboole_0, k3_xboole_0(A_26, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_1624, c_4480])).
% 8.44/3.36  tff(c_4658, plain, (![A_26, B_27]: (k5_xboole_0(k4_xboole_0(A_26, B_27), A_26)=k3_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_4580])).
% 8.44/3.36  tff(c_6585, plain, (k5_xboole_0(k1_xboole_0, '#skF_5')=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6578, c_4658])).
% 8.44/3.36  tff(c_6621, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_146, c_6585])).
% 8.44/3.36  tff(c_66, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.44/3.36  tff(c_2424, plain, (r2_hidden('#skF_4'('#skF_5'), '#skF_6') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_2408])).
% 8.44/3.36  tff(c_2430, plain, (r2_hidden('#skF_4'('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_2424])).
% 8.44/3.36  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.44/3.36  tff(c_2446, plain, (![B_233]: (r2_hidden('#skF_4'('#skF_5'), B_233) | ~r1_tarski('#skF_6', B_233))), inference(resolution, [status(thm)], [c_2430, c_6])).
% 8.44/3.36  tff(c_343, plain, (![A_99, B_100, C_101]: (~r1_xboole_0(A_99, B_100) | ~r2_hidden(C_101, k3_xboole_0(A_99, B_100)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.44/3.36  tff(c_349, plain, (![B_2, A_1, C_101]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_101, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_343])).
% 8.44/3.36  tff(c_2467, plain, (![B_2, A_1]: (~r1_xboole_0(B_2, A_1) | ~r1_tarski('#skF_6', k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2446, c_349])).
% 8.44/3.36  tff(c_6647, plain, (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_tarski('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6621, c_2467])).
% 8.44/3.36  tff(c_7295, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_6647])).
% 8.44/3.36  tff(c_1219, plain, (![A_166, C_167, B_168, D_169]: (r2_hidden(A_166, C_167) | ~r2_hidden(k4_tarski(A_166, B_168), k2_zfmisc_1(C_167, D_169)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.44/3.36  tff(c_1222, plain, (![A_166, B_168]: (r2_hidden(A_166, '#skF_5') | ~r2_hidden(k4_tarski(A_166, B_168), k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1219])).
% 8.44/3.36  tff(c_2122, plain, (![A_201, B_202]: (r2_hidden(A_201, '#skF_5') | ~r2_hidden(B_202, '#skF_5') | ~r2_hidden(A_201, '#skF_6'))), inference(resolution, [status(thm)], [c_2102, c_1222])).
% 8.44/3.36  tff(c_2478, plain, (![B_234]: (~r2_hidden(B_234, '#skF_5'))), inference(splitLeft, [status(thm)], [c_2122])).
% 8.44/3.36  tff(c_2498, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_2478])).
% 8.44/3.36  tff(c_2506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_2498])).
% 8.44/3.36  tff(c_2508, plain, (![A_235]: (r2_hidden(A_235, '#skF_5') | ~r2_hidden(A_235, '#skF_6'))), inference(splitRight, [status(thm)], [c_2122])).
% 8.44/3.36  tff(c_15218, plain, (![A_451]: (r1_tarski(A_451, '#skF_5') | ~r2_hidden('#skF_1'(A_451, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_2508, c_8])).
% 8.44/3.36  tff(c_15230, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_10, c_15218])).
% 8.44/3.36  tff(c_15237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7295, c_7295, c_15230])).
% 8.44/3.36  tff(c_15239, plain, (r1_tarski('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_6647])).
% 8.44/3.36  tff(c_15248, plain, (k4_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_15239, c_26])).
% 8.44/3.36  tff(c_574, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k3_xboole_0(A_114, B_115))=k4_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.44/3.36  tff(c_606, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_574])).
% 8.44/3.36  tff(c_4673, plain, (![B_292, A_293]: (k5_xboole_0(B_292, k4_xboole_0(B_292, A_293))=k3_xboole_0(A_293, B_292))), inference(superposition, [status(thm), theory('equality')], [c_606, c_1573])).
% 8.44/3.36  tff(c_1637, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1573])).
% 8.44/3.36  tff(c_4712, plain, (![B_292, A_293]: (k5_xboole_0(k4_xboole_0(B_292, A_293), k3_xboole_0(A_293, B_292))=B_292)), inference(superposition, [status(thm), theory('equality')], [c_4673, c_1637])).
% 8.44/3.36  tff(c_15260, plain, (k5_xboole_0(k1_xboole_0, k3_xboole_0('#skF_5', '#skF_6'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_15248, c_4712])).
% 8.44/3.36  tff(c_15299, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_6621, c_2, c_15260])).
% 8.44/3.36  tff(c_15301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_15299])).
% 8.44/3.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.44/3.36  
% 8.44/3.36  Inference rules
% 8.44/3.36  ----------------------
% 8.44/3.36  #Ref     : 1
% 8.44/3.36  #Sup     : 3856
% 8.44/3.36  #Fact    : 0
% 8.44/3.36  #Define  : 0
% 8.44/3.36  #Split   : 11
% 8.44/3.36  #Chain   : 0
% 8.44/3.36  #Close   : 0
% 8.44/3.36  
% 8.44/3.36  Ordering : KBO
% 8.44/3.36  
% 8.44/3.36  Simplification rules
% 8.44/3.36  ----------------------
% 8.44/3.36  #Subsume      : 680
% 8.44/3.36  #Demod        : 2963
% 8.44/3.36  #Tautology    : 1661
% 8.44/3.36  #SimpNegUnit  : 88
% 8.44/3.36  #BackRed      : 19
% 8.44/3.36  
% 8.44/3.36  #Partial instantiations: 0
% 8.44/3.36  #Strategies tried      : 1
% 8.44/3.36  
% 8.44/3.36  Timing (in seconds)
% 8.44/3.36  ----------------------
% 8.44/3.37  Preprocessing        : 0.34
% 8.44/3.37  Parsing              : 0.19
% 8.44/3.37  CNF conversion       : 0.02
% 8.44/3.37  Main loop            : 2.17
% 8.44/3.37  Inferencing          : 0.49
% 8.44/3.37  Reduction            : 1.11
% 8.44/3.37  Demodulation         : 0.94
% 8.44/3.37  BG Simplification    : 0.06
% 8.44/3.37  Subsumption          : 0.36
% 8.44/3.37  Abstraction          : 0.08
% 8.44/3.37  MUC search           : 0.00
% 8.44/3.37  Cooper               : 0.00
% 8.44/3.37  Total                : 2.55
% 8.44/3.37  Index Insertion      : 0.00
% 8.44/3.37  Index Deletion       : 0.00
% 8.44/3.37  Index Matching       : 0.00
% 8.44/3.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
