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
% DateTime   : Thu Dec  3 10:06:09 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 5.59s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 313 expanded)
%              Number of leaves         :   22 ( 110 expanded)
%              Depth                    :   12
%              Number of atoms          :  168 ( 830 expanded)
%              Number of equality atoms :   18 (  71 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_73,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_69,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    ! [A_19] :
      ( v3_ordinal1(k1_ordinal1(A_19))
      | ~ v3_ordinal1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_451,plain,(
    ! [B_72,A_73] :
      ( r2_hidden(B_72,A_73)
      | r1_ordinal1(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_73,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_484,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_451,c_73])).

tff(c_498,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_484])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ r1_ordinal1(A_12,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_601,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(A_81,B_82)
      | ~ r1_ordinal1(A_81,B_82)
      | ~ v3_ordinal1(B_82)
      | ~ v3_ordinal1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_888,plain,(
    ! [B_101,A_102] :
      ( B_101 = A_102
      | ~ r1_tarski(B_101,A_102)
      | ~ r1_ordinal1(A_102,B_101)
      | ~ v3_ordinal1(B_101)
      | ~ v3_ordinal1(A_102) ) ),
    inference(resolution,[status(thm)],[c_601,c_4])).

tff(c_2884,plain,(
    ! [B_219,A_220] :
      ( B_219 = A_220
      | ~ r1_ordinal1(B_219,A_220)
      | ~ r1_ordinal1(A_220,B_219)
      | ~ v3_ordinal1(B_219)
      | ~ v3_ordinal1(A_220) ) ),
    inference(resolution,[status(thm)],[c_20,c_888])).

tff(c_2898,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_498,c_2884])).

tff(c_2911,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2898])).

tff(c_2917,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2911])).

tff(c_28,plain,(
    ! [B_18,A_16] :
      ( r2_hidden(B_18,A_16)
      | r1_ordinal1(A_16,B_18)
      | ~ v3_ordinal1(B_18)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_79,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_44])).

tff(c_2902,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_79,c_2884])).

tff(c_2916,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2902])).

tff(c_2970,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2916])).

tff(c_2973,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2970])).

tff(c_2977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2973])).

tff(c_2979,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2916])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden(A_14,B_15)
      | r2_hidden(A_14,k1_ordinal1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_778,plain,(
    ! [A_92,B_93] :
      ( ~ r2_hidden(A_92,B_93)
      | r1_ordinal1(A_92,B_93)
      | ~ v3_ordinal1(B_93)
      | ~ v3_ordinal1(A_92) ) ),
    inference(resolution,[status(thm)],[c_451,c_2])).

tff(c_789,plain,(
    ! [A_14,B_15] :
      ( r1_ordinal1(A_14,k1_ordinal1(B_15))
      | ~ v3_ordinal1(k1_ordinal1(B_15))
      | ~ v3_ordinal1(A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_26,c_778])).

tff(c_2978,plain,
    ( ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | k1_ordinal1('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2916])).

tff(c_2980,plain,(
    ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2978])).

tff(c_2983,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2')
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_789,c_2980])).

tff(c_2988,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2979,c_2983])).

tff(c_2991,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2988])).

tff(c_2994,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2991])).

tff(c_2996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2917,c_2994])).

tff(c_2997,plain,(
    k1_ordinal1('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2978])).

tff(c_24,plain,(
    ! [B_15] : r2_hidden(B_15,k1_ordinal1(B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_790,plain,(
    ! [B_15] :
      ( r1_ordinal1(B_15,k1_ordinal1(B_15))
      | ~ v3_ordinal1(k1_ordinal1(B_15))
      | ~ v3_ordinal1(B_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_778])).

tff(c_3056,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2997,c_790])).

tff(c_3198,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2997,c_3056])).

tff(c_3200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2917,c_3198])).

tff(c_3201,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2911])).

tff(c_3204,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_79])).

tff(c_67,plain,(
    ! [B_28,A_29] :
      ( ~ r1_tarski(B_28,A_29)
      | ~ r2_hidden(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71,plain,(
    ! [B_15] : ~ r1_tarski(k1_ordinal1(B_15),B_15) ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_628,plain,(
    ! [B_82] :
      ( ~ r1_ordinal1(k1_ordinal1(B_82),B_82)
      | ~ v3_ordinal1(B_82)
      | ~ v3_ordinal1(k1_ordinal1(B_82)) ) ),
    inference(resolution,[status(thm)],[c_601,c_71])).

tff(c_3230,plain,
    ( ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3204,c_628])).

tff(c_3236,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3230])).

tff(c_3239,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3236])).

tff(c_3243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3239])).

tff(c_3245,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_3250,plain,(
    ! [B_224,A_225] :
      ( ~ r2_hidden(B_224,A_225)
      | ~ r2_hidden(A_225,B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3255,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_3245,c_3250])).

tff(c_3605,plain,(
    ! [B_264,A_265] :
      ( r2_hidden(B_264,A_265)
      | r1_ordinal1(A_265,B_264)
      | ~ v3_ordinal1(B_264)
      | ~ v3_ordinal1(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | r2_hidden(A_14,B_15)
      | ~ r2_hidden(A_14,k1_ordinal1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4884,plain,(
    ! [B_337,B_336] :
      ( B_337 = B_336
      | r2_hidden(B_336,B_337)
      | r1_ordinal1(k1_ordinal1(B_337),B_336)
      | ~ v3_ordinal1(B_336)
      | ~ v3_ordinal1(k1_ordinal1(B_337)) ) ),
    inference(resolution,[status(thm)],[c_3605,c_22])).

tff(c_3244,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_4887,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4884,c_3244])).

tff(c_4890,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4887])).

tff(c_4891,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_3255,c_4890])).

tff(c_4892,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4891])).

tff(c_4895,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4892])).

tff(c_4899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4895])).

tff(c_4900,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4891])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3249,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_3245,c_32])).

tff(c_4906,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4900,c_3249])).

tff(c_4911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.59/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.59/2.07  
% 5.59/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.59/2.07  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 5.59/2.07  
% 5.59/2.07  %Foreground sorts:
% 5.59/2.07  
% 5.59/2.07  
% 5.59/2.07  %Background operators:
% 5.59/2.07  
% 5.59/2.07  
% 5.59/2.07  %Foreground operators:
% 5.59/2.07  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.59/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.59/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.59/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.59/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.59/2.07  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.59/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.59/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.59/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.59/2.07  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.59/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.59/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.59/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.59/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.59/2.07  
% 5.59/2.09  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.59/2.09  tff(f_88, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 5.59/2.09  tff(f_73, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 5.59/2.09  tff(f_69, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 5.59/2.09  tff(f_54, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.59/2.09  tff(f_60, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 5.59/2.09  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 5.59/2.09  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.59/2.09  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.59/2.09  tff(c_36, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.59/2.09  tff(c_30, plain, (![A_19]: (v3_ordinal1(k1_ordinal1(A_19)) | ~v3_ordinal1(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.59/2.09  tff(c_34, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.59/2.09  tff(c_451, plain, (![B_72, A_73]: (r2_hidden(B_72, A_73) | r1_ordinal1(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.59/2.09  tff(c_38, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.59/2.09  tff(c_73, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 5.59/2.09  tff(c_484, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_451, c_73])).
% 5.59/2.09  tff(c_498, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_484])).
% 5.59/2.09  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~r1_ordinal1(A_12, B_13) | ~v3_ordinal1(B_13) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.59/2.09  tff(c_601, plain, (![A_81, B_82]: (r1_tarski(A_81, B_82) | ~r1_ordinal1(A_81, B_82) | ~v3_ordinal1(B_82) | ~v3_ordinal1(A_81))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.59/2.09  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.59/2.09  tff(c_888, plain, (![B_101, A_102]: (B_101=A_102 | ~r1_tarski(B_101, A_102) | ~r1_ordinal1(A_102, B_101) | ~v3_ordinal1(B_101) | ~v3_ordinal1(A_102))), inference(resolution, [status(thm)], [c_601, c_4])).
% 5.59/2.09  tff(c_2884, plain, (![B_219, A_220]: (B_219=A_220 | ~r1_ordinal1(B_219, A_220) | ~r1_ordinal1(A_220, B_219) | ~v3_ordinal1(B_219) | ~v3_ordinal1(A_220))), inference(resolution, [status(thm)], [c_20, c_888])).
% 5.59/2.09  tff(c_2898, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_498, c_2884])).
% 5.59/2.09  tff(c_2911, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2898])).
% 5.59/2.09  tff(c_2917, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_2911])).
% 5.59/2.09  tff(c_28, plain, (![B_18, A_16]: (r2_hidden(B_18, A_16) | r1_ordinal1(A_16, B_18) | ~v3_ordinal1(B_18) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.59/2.09  tff(c_44, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.59/2.09  tff(c_79, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_73, c_44])).
% 5.59/2.09  tff(c_2902, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_79, c_2884])).
% 5.59/2.09  tff(c_2916, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2902])).
% 5.59/2.09  tff(c_2970, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2916])).
% 5.59/2.09  tff(c_2973, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2970])).
% 5.59/2.09  tff(c_2977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2973])).
% 5.59/2.09  tff(c_2979, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_2916])).
% 5.59/2.09  tff(c_26, plain, (![A_14, B_15]: (~r2_hidden(A_14, B_15) | r2_hidden(A_14, k1_ordinal1(B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.59/2.09  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.59/2.09  tff(c_778, plain, (![A_92, B_93]: (~r2_hidden(A_92, B_93) | r1_ordinal1(A_92, B_93) | ~v3_ordinal1(B_93) | ~v3_ordinal1(A_92))), inference(resolution, [status(thm)], [c_451, c_2])).
% 5.59/2.09  tff(c_789, plain, (![A_14, B_15]: (r1_ordinal1(A_14, k1_ordinal1(B_15)) | ~v3_ordinal1(k1_ordinal1(B_15)) | ~v3_ordinal1(A_14) | ~r2_hidden(A_14, B_15))), inference(resolution, [status(thm)], [c_26, c_778])).
% 5.59/2.09  tff(c_2978, plain, (~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | k1_ordinal1('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_2916])).
% 5.59/2.09  tff(c_2980, plain, (~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2978])).
% 5.59/2.09  tff(c_2983, plain, (~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2') | ~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_789, c_2980])).
% 5.59/2.09  tff(c_2988, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2979, c_2983])).
% 5.59/2.09  tff(c_2991, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2988])).
% 5.59/2.09  tff(c_2994, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2991])).
% 5.59/2.09  tff(c_2996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2917, c_2994])).
% 5.59/2.09  tff(c_2997, plain, (k1_ordinal1('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_2978])).
% 5.59/2.09  tff(c_24, plain, (![B_15]: (r2_hidden(B_15, k1_ordinal1(B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.59/2.09  tff(c_790, plain, (![B_15]: (r1_ordinal1(B_15, k1_ordinal1(B_15)) | ~v3_ordinal1(k1_ordinal1(B_15)) | ~v3_ordinal1(B_15))), inference(resolution, [status(thm)], [c_24, c_778])).
% 5.59/2.09  tff(c_3056, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2997, c_790])).
% 5.59/2.09  tff(c_3198, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2997, c_3056])).
% 5.59/2.09  tff(c_3200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2917, c_3198])).
% 5.59/2.09  tff(c_3201, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_2911])).
% 5.59/2.09  tff(c_3204, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_79])).
% 5.59/2.09  tff(c_67, plain, (![B_28, A_29]: (~r1_tarski(B_28, A_29) | ~r2_hidden(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.59/2.09  tff(c_71, plain, (![B_15]: (~r1_tarski(k1_ordinal1(B_15), B_15))), inference(resolution, [status(thm)], [c_24, c_67])).
% 5.59/2.09  tff(c_628, plain, (![B_82]: (~r1_ordinal1(k1_ordinal1(B_82), B_82) | ~v3_ordinal1(B_82) | ~v3_ordinal1(k1_ordinal1(B_82)))), inference(resolution, [status(thm)], [c_601, c_71])).
% 5.59/2.09  tff(c_3230, plain, (~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_3204, c_628])).
% 5.59/2.09  tff(c_3236, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3230])).
% 5.59/2.09  tff(c_3239, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3236])).
% 5.59/2.09  tff(c_3243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_3239])).
% 5.59/2.09  tff(c_3245, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 5.59/2.09  tff(c_3250, plain, (![B_224, A_225]: (~r2_hidden(B_224, A_225) | ~r2_hidden(A_225, B_224))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.59/2.09  tff(c_3255, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_3245, c_3250])).
% 5.59/2.09  tff(c_3605, plain, (![B_264, A_265]: (r2_hidden(B_264, A_265) | r1_ordinal1(A_265, B_264) | ~v3_ordinal1(B_264) | ~v3_ordinal1(A_265))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.59/2.09  tff(c_22, plain, (![B_15, A_14]: (B_15=A_14 | r2_hidden(A_14, B_15) | ~r2_hidden(A_14, k1_ordinal1(B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.59/2.09  tff(c_4884, plain, (![B_337, B_336]: (B_337=B_336 | r2_hidden(B_336, B_337) | r1_ordinal1(k1_ordinal1(B_337), B_336) | ~v3_ordinal1(B_336) | ~v3_ordinal1(k1_ordinal1(B_337)))), inference(resolution, [status(thm)], [c_3605, c_22])).
% 5.59/2.09  tff(c_3244, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 5.59/2.09  tff(c_4887, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_4884, c_3244])).
% 5.59/2.09  tff(c_4890, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4887])).
% 5.59/2.09  tff(c_4891, plain, ('#skF_2'='#skF_1' | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_3255, c_4890])).
% 5.59/2.09  tff(c_4892, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_4891])).
% 5.59/2.09  tff(c_4895, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_4892])).
% 5.59/2.09  tff(c_4899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_4895])).
% 5.59/2.09  tff(c_4900, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_4891])).
% 5.59/2.09  tff(c_32, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.59/2.09  tff(c_3249, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_3245, c_32])).
% 5.59/2.09  tff(c_4906, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4900, c_3249])).
% 5.59/2.09  tff(c_4911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_4906])).
% 5.59/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.59/2.09  
% 5.59/2.09  Inference rules
% 5.59/2.09  ----------------------
% 5.59/2.09  #Ref     : 0
% 5.59/2.09  #Sup     : 1061
% 5.59/2.09  #Fact    : 2
% 5.59/2.09  #Define  : 0
% 5.59/2.09  #Split   : 5
% 5.59/2.09  #Chain   : 0
% 5.59/2.09  #Close   : 0
% 5.59/2.09  
% 5.59/2.09  Ordering : KBO
% 5.59/2.09  
% 5.59/2.09  Simplification rules
% 5.59/2.09  ----------------------
% 5.59/2.09  #Subsume      : 79
% 5.59/2.09  #Demod        : 197
% 5.59/2.09  #Tautology    : 178
% 5.59/2.09  #SimpNegUnit  : 5
% 5.59/2.09  #BackRed      : 13
% 5.59/2.09  
% 5.59/2.09  #Partial instantiations: 0
% 5.59/2.09  #Strategies tried      : 1
% 5.59/2.09  
% 5.59/2.09  Timing (in seconds)
% 5.59/2.09  ----------------------
% 5.59/2.09  Preprocessing        : 0.32
% 5.59/2.09  Parsing              : 0.17
% 5.59/2.09  CNF conversion       : 0.02
% 5.59/2.09  Main loop            : 1.00
% 5.59/2.09  Inferencing          : 0.32
% 5.59/2.09  Reduction            : 0.36
% 5.59/2.09  Demodulation         : 0.27
% 5.59/2.09  BG Simplification    : 0.04
% 5.59/2.09  Subsumption          : 0.20
% 5.59/2.09  Abstraction          : 0.05
% 5.59/2.10  MUC search           : 0.00
% 5.59/2.10  Cooper               : 0.00
% 5.59/2.10  Total                : 1.36
% 5.59/2.10  Index Insertion      : 0.00
% 5.59/2.10  Index Deletion       : 0.00
% 5.59/2.10  Index Matching       : 0.00
% 5.59/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
