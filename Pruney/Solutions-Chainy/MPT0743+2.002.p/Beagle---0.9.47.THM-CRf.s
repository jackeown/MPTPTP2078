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
% DateTime   : Thu Dec  3 10:06:08 EST 2020

% Result     : Theorem 32.08s
% Output     : CNFRefutation 32.18s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 197 expanded)
%              Number of leaves         :   32 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  167 ( 435 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_115,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_69,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_111,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_120,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(c_32,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_76,plain,(
    ! [A_34] :
      ( v3_ordinal1(k1_ordinal1(A_34))
      | ~ v3_ordinal1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_82,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_64,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ r1_ordinal1(A_24,B_25)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_94,plain,(
    ! [A_40] :
      ( v1_ordinal1(A_40)
      | ~ v3_ordinal1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_102,plain,(
    v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_94])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r2_xboole_0(A_9,B_10)
      | B_10 = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1108,plain,(
    ! [A_156,B_157] :
      ( r2_hidden(A_156,B_157)
      | ~ r2_xboole_0(A_156,B_157)
      | ~ v3_ordinal1(B_157)
      | ~ v1_ordinal1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4339,plain,(
    ! [A_403,B_404] :
      ( r2_hidden(A_403,B_404)
      | ~ v3_ordinal1(B_404)
      | ~ v1_ordinal1(A_403)
      | B_404 = A_403
      | ~ r1_tarski(A_403,B_404) ) ),
    inference(resolution,[status(thm)],[c_22,c_1108])).

tff(c_84,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_4844,plain,
    ( ~ v3_ordinal1('#skF_6')
    | ~ v1_ordinal1('#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_4339,c_112])).

tff(c_4983,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_80,c_4844])).

tff(c_4984,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4983])).

tff(c_4987,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_4984])).

tff(c_4990,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_4987])).

tff(c_74,plain,(
    ! [B_33,A_31] :
      ( r2_hidden(B_33,A_31)
      | r1_ordinal1(A_31,B_33)
      | ~ v3_ordinal1(B_33)
      | ~ v3_ordinal1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_90,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r1_ordinal1(k1_ordinal1('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_142,plain,(
    r1_ordinal1(k1_ordinal1('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_90])).

tff(c_739,plain,(
    ! [A_134,B_135] :
      ( r1_tarski(A_134,B_135)
      | ~ r1_ordinal1(A_134,B_135)
      | ~ v3_ordinal1(B_135)
      | ~ v3_ordinal1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_205,plain,(
    ! [A_71,B_72] :
      ( ~ r2_hidden(A_71,B_72)
      | r2_hidden(A_71,k1_ordinal1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_78,plain,(
    ! [B_36,A_35] :
      ( ~ r1_tarski(B_36,A_35)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_232,plain,(
    ! [B_72,A_71] :
      ( ~ r1_tarski(k1_ordinal1(B_72),A_71)
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_205,c_78])).

tff(c_47563,plain,(
    ! [B_3036,B_3037] :
      ( ~ r2_hidden(B_3036,B_3037)
      | ~ r1_ordinal1(k1_ordinal1(B_3037),B_3036)
      | ~ v3_ordinal1(B_3036)
      | ~ v3_ordinal1(k1_ordinal1(B_3037)) ) ),
    inference(resolution,[status(thm)],[c_739,c_232])).

tff(c_47629,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_142,c_47563])).

tff(c_47648,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_47629])).

tff(c_47649,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_47648])).

tff(c_47652,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_47649])).

tff(c_47656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_47652])).

tff(c_47657,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_47648])).

tff(c_47672,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_47657])).

tff(c_47678,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_47672])).

tff(c_47680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4990,c_47678])).

tff(c_47681,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4983])).

tff(c_47684,plain,(
    r1_ordinal1(k1_ordinal1('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47681,c_142])).

tff(c_68,plain,(
    ! [B_27] : r2_hidden(B_27,k1_ordinal1(B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_154,plain,(
    ! [B_53,A_54] :
      ( ~ r1_tarski(B_53,A_54)
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_170,plain,(
    ! [B_27] : ~ r1_tarski(k1_ordinal1(B_27),B_27) ),
    inference(resolution,[status(thm)],[c_68,c_154])).

tff(c_48010,plain,(
    ! [B_3066] :
      ( ~ r1_ordinal1(k1_ordinal1(B_3066),B_3066)
      | ~ v3_ordinal1(B_3066)
      | ~ v3_ordinal1(k1_ordinal1(B_3066)) ) ),
    inference(resolution,[status(thm)],[c_739,c_170])).

tff(c_48017,plain,
    ( ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1(k1_ordinal1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_47684,c_48010])).

tff(c_48030,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_48017])).

tff(c_48035,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_48030])).

tff(c_48039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_48035])).

tff(c_48041,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_48116,plain,(
    ! [B_3088,A_3089] :
      ( ~ r2_hidden(B_3088,A_3089)
      | ~ r2_hidden(A_3089,B_3088) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_48131,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48041,c_48116])).

tff(c_49063,plain,(
    ! [B_3184,A_3185] :
      ( r1_ordinal1(B_3184,A_3185)
      | r1_ordinal1(A_3185,B_3184)
      | ~ v3_ordinal1(B_3184)
      | ~ v3_ordinal1(A_3185) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_48040,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_49066,plain,
    ( r1_ordinal1('#skF_6',k1_ordinal1('#skF_5'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_5'))
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_49063,c_48040])).

tff(c_49072,plain,
    ( r1_ordinal1('#skF_6',k1_ordinal1('#skF_5'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_49066])).

tff(c_49076,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_49072])).

tff(c_49079,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_49076])).

tff(c_49083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_49079])).

tff(c_49085,plain,(
    v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_49072])).

tff(c_48758,plain,(
    ! [B_3170,A_3171] :
      ( r2_hidden(B_3170,A_3171)
      | r1_ordinal1(A_3171,B_3170)
      | ~ v3_ordinal1(B_3170)
      | ~ v3_ordinal1(A_3171) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_66,plain,(
    ! [B_27,A_26] :
      ( B_27 = A_26
      | r2_hidden(A_26,B_27)
      | ~ r2_hidden(A_26,k1_ordinal1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_53347,plain,(
    ! [B_3461,B_3460] :
      ( B_3461 = B_3460
      | r2_hidden(B_3460,B_3461)
      | r1_ordinal1(k1_ordinal1(B_3461),B_3460)
      | ~ v3_ordinal1(B_3460)
      | ~ v3_ordinal1(k1_ordinal1(B_3461)) ) ),
    inference(resolution,[status(thm)],[c_48758,c_66])).

tff(c_53354,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_53347,c_48040])).

tff(c_53359,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49085,c_80,c_53354])).

tff(c_53360,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_48131,c_53359])).

tff(c_48076,plain,(
    ! [B_3079,A_3080] :
      ( ~ r1_tarski(B_3079,A_3080)
      | ~ r2_hidden(A_3080,B_3079) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48096,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48041,c_48076])).

tff(c_53368,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53360,c_48096])).

tff(c_53376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_53368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 14:00:07 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.08/19.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.08/19.18  
% 32.08/19.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.08/19.18  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 32.08/19.18  
% 32.08/19.18  %Foreground sorts:
% 32.08/19.18  
% 32.08/19.18  
% 32.08/19.18  %Background operators:
% 32.08/19.18  
% 32.08/19.18  
% 32.08/19.18  %Foreground operators:
% 32.08/19.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 32.08/19.18  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 32.08/19.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.08/19.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 32.08/19.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 32.08/19.18  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 32.08/19.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 32.08/19.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.08/19.18  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 32.08/19.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 32.08/19.18  tff('#skF_5', type, '#skF_5': $i).
% 32.08/19.18  tff('#skF_6', type, '#skF_6': $i).
% 32.08/19.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 32.08/19.18  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 32.08/19.18  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 32.08/19.18  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 32.08/19.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.08/19.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 32.08/19.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.08/19.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 32.08/19.18  
% 32.18/19.20  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 32.18/19.20  tff(f_130, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 32.18/19.20  tff(f_115, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 32.18/19.20  tff(f_87, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 32.18/19.20  tff(f_69, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 32.18/19.20  tff(f_46, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 32.18/19.20  tff(f_102, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 32.18/19.20  tff(f_111, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 32.18/19.20  tff(f_93, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 32.18/19.20  tff(f_120, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 32.18/19.20  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 32.18/19.20  tff(f_77, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 32.18/19.20  tff(c_32, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 32.18/19.20  tff(c_80, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 32.18/19.20  tff(c_76, plain, (![A_34]: (v3_ordinal1(k1_ordinal1(A_34)) | ~v3_ordinal1(A_34))), inference(cnfTransformation, [status(thm)], [f_115])).
% 32.18/19.20  tff(c_82, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 32.18/19.20  tff(c_64, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~r1_ordinal1(A_24, B_25) | ~v3_ordinal1(B_25) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 32.18/19.20  tff(c_94, plain, (![A_40]: (v1_ordinal1(A_40) | ~v3_ordinal1(A_40))), inference(cnfTransformation, [status(thm)], [f_69])).
% 32.18/19.20  tff(c_102, plain, (v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_94])).
% 32.18/19.20  tff(c_22, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 32.18/19.20  tff(c_1108, plain, (![A_156, B_157]: (r2_hidden(A_156, B_157) | ~r2_xboole_0(A_156, B_157) | ~v3_ordinal1(B_157) | ~v1_ordinal1(A_156))), inference(cnfTransformation, [status(thm)], [f_102])).
% 32.18/19.20  tff(c_4339, plain, (![A_403, B_404]: (r2_hidden(A_403, B_404) | ~v3_ordinal1(B_404) | ~v1_ordinal1(A_403) | B_404=A_403 | ~r1_tarski(A_403, B_404))), inference(resolution, [status(thm)], [c_22, c_1108])).
% 32.18/19.20  tff(c_84, plain, (~r1_ordinal1(k1_ordinal1('#skF_5'), '#skF_6') | ~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 32.18/19.20  tff(c_112, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_84])).
% 32.18/19.20  tff(c_4844, plain, (~v3_ordinal1('#skF_6') | ~v1_ordinal1('#skF_5') | '#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_4339, c_112])).
% 32.18/19.20  tff(c_4983, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_80, c_4844])).
% 32.18/19.20  tff(c_4984, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_4983])).
% 32.18/19.20  tff(c_4987, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_4984])).
% 32.18/19.20  tff(c_4990, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_4987])).
% 32.18/19.20  tff(c_74, plain, (![B_33, A_31]: (r2_hidden(B_33, A_31) | r1_ordinal1(A_31, B_33) | ~v3_ordinal1(B_33) | ~v3_ordinal1(A_31))), inference(cnfTransformation, [status(thm)], [f_111])).
% 32.18/19.20  tff(c_90, plain, (r2_hidden('#skF_5', '#skF_6') | r1_ordinal1(k1_ordinal1('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 32.18/19.20  tff(c_142, plain, (r1_ordinal1(k1_ordinal1('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_112, c_90])).
% 32.18/19.20  tff(c_739, plain, (![A_134, B_135]: (r1_tarski(A_134, B_135) | ~r1_ordinal1(A_134, B_135) | ~v3_ordinal1(B_135) | ~v3_ordinal1(A_134))), inference(cnfTransformation, [status(thm)], [f_87])).
% 32.18/19.20  tff(c_205, plain, (![A_71, B_72]: (~r2_hidden(A_71, B_72) | r2_hidden(A_71, k1_ordinal1(B_72)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 32.18/19.20  tff(c_78, plain, (![B_36, A_35]: (~r1_tarski(B_36, A_35) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_120])).
% 32.18/19.20  tff(c_232, plain, (![B_72, A_71]: (~r1_tarski(k1_ordinal1(B_72), A_71) | ~r2_hidden(A_71, B_72))), inference(resolution, [status(thm)], [c_205, c_78])).
% 32.18/19.20  tff(c_47563, plain, (![B_3036, B_3037]: (~r2_hidden(B_3036, B_3037) | ~r1_ordinal1(k1_ordinal1(B_3037), B_3036) | ~v3_ordinal1(B_3036) | ~v3_ordinal1(k1_ordinal1(B_3037)))), inference(resolution, [status(thm)], [c_739, c_232])).
% 32.18/19.20  tff(c_47629, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_142, c_47563])).
% 32.18/19.20  tff(c_47648, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_47629])).
% 32.18/19.20  tff(c_47649, plain, (~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(splitLeft, [status(thm)], [c_47648])).
% 32.18/19.20  tff(c_47652, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_47649])).
% 32.18/19.20  tff(c_47656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_47652])).
% 32.18/19.20  tff(c_47657, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_47648])).
% 32.18/19.20  tff(c_47672, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_47657])).
% 32.18/19.20  tff(c_47678, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_47672])).
% 32.18/19.20  tff(c_47680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4990, c_47678])).
% 32.18/19.20  tff(c_47681, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_4983])).
% 32.18/19.20  tff(c_47684, plain, (r1_ordinal1(k1_ordinal1('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_47681, c_142])).
% 32.18/19.20  tff(c_68, plain, (![B_27]: (r2_hidden(B_27, k1_ordinal1(B_27)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 32.18/19.20  tff(c_154, plain, (![B_53, A_54]: (~r1_tarski(B_53, A_54) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_120])).
% 32.18/19.20  tff(c_170, plain, (![B_27]: (~r1_tarski(k1_ordinal1(B_27), B_27))), inference(resolution, [status(thm)], [c_68, c_154])).
% 32.18/19.20  tff(c_48010, plain, (![B_3066]: (~r1_ordinal1(k1_ordinal1(B_3066), B_3066) | ~v3_ordinal1(B_3066) | ~v3_ordinal1(k1_ordinal1(B_3066)))), inference(resolution, [status(thm)], [c_739, c_170])).
% 32.18/19.20  tff(c_48017, plain, (~v3_ordinal1('#skF_6') | ~v3_ordinal1(k1_ordinal1('#skF_6'))), inference(resolution, [status(thm)], [c_47684, c_48010])).
% 32.18/19.20  tff(c_48030, plain, (~v3_ordinal1(k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_48017])).
% 32.18/19.20  tff(c_48035, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_48030])).
% 32.18/19.20  tff(c_48039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_48035])).
% 32.18/19.20  tff(c_48041, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_84])).
% 32.18/19.20  tff(c_48116, plain, (![B_3088, A_3089]: (~r2_hidden(B_3088, A_3089) | ~r2_hidden(A_3089, B_3088))), inference(cnfTransformation, [status(thm)], [f_30])).
% 32.18/19.20  tff(c_48131, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48041, c_48116])).
% 32.18/19.20  tff(c_49063, plain, (![B_3184, A_3185]: (r1_ordinal1(B_3184, A_3185) | r1_ordinal1(A_3185, B_3184) | ~v3_ordinal1(B_3184) | ~v3_ordinal1(A_3185))), inference(cnfTransformation, [status(thm)], [f_77])).
% 32.18/19.20  tff(c_48040, plain, (~r1_ordinal1(k1_ordinal1('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_84])).
% 32.18/19.20  tff(c_49066, plain, (r1_ordinal1('#skF_6', k1_ordinal1('#skF_5')) | ~v3_ordinal1(k1_ordinal1('#skF_5')) | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_49063, c_48040])).
% 32.18/19.20  tff(c_49072, plain, (r1_ordinal1('#skF_6', k1_ordinal1('#skF_5')) | ~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_49066])).
% 32.18/19.20  tff(c_49076, plain, (~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(splitLeft, [status(thm)], [c_49072])).
% 32.18/19.20  tff(c_49079, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_49076])).
% 32.18/19.20  tff(c_49083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_49079])).
% 32.18/19.20  tff(c_49085, plain, (v3_ordinal1(k1_ordinal1('#skF_5'))), inference(splitRight, [status(thm)], [c_49072])).
% 32.18/19.20  tff(c_48758, plain, (![B_3170, A_3171]: (r2_hidden(B_3170, A_3171) | r1_ordinal1(A_3171, B_3170) | ~v3_ordinal1(B_3170) | ~v3_ordinal1(A_3171))), inference(cnfTransformation, [status(thm)], [f_111])).
% 32.18/19.20  tff(c_66, plain, (![B_27, A_26]: (B_27=A_26 | r2_hidden(A_26, B_27) | ~r2_hidden(A_26, k1_ordinal1(B_27)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 32.18/19.20  tff(c_53347, plain, (![B_3461, B_3460]: (B_3461=B_3460 | r2_hidden(B_3460, B_3461) | r1_ordinal1(k1_ordinal1(B_3461), B_3460) | ~v3_ordinal1(B_3460) | ~v3_ordinal1(k1_ordinal1(B_3461)))), inference(resolution, [status(thm)], [c_48758, c_66])).
% 32.18/19.20  tff(c_53354, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_53347, c_48040])).
% 32.18/19.20  tff(c_53359, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_49085, c_80, c_53354])).
% 32.18/19.20  tff(c_53360, plain, ('#skF_5'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_48131, c_53359])).
% 32.18/19.20  tff(c_48076, plain, (![B_3079, A_3080]: (~r1_tarski(B_3079, A_3080) | ~r2_hidden(A_3080, B_3079))), inference(cnfTransformation, [status(thm)], [f_120])).
% 32.18/19.20  tff(c_48096, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48041, c_48076])).
% 32.18/19.20  tff(c_53368, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_53360, c_48096])).
% 32.18/19.20  tff(c_53376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_53368])).
% 32.18/19.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.18/19.20  
% 32.18/19.20  Inference rules
% 32.18/19.20  ----------------------
% 32.18/19.20  #Ref     : 0
% 32.18/19.20  #Sup     : 11317
% 32.18/19.20  #Fact    : 60
% 32.18/19.20  #Define  : 0
% 32.18/19.20  #Split   : 4
% 32.18/19.20  #Chain   : 0
% 32.18/19.20  #Close   : 0
% 32.18/19.20  
% 32.18/19.20  Ordering : KBO
% 32.18/19.20  
% 32.18/19.20  Simplification rules
% 32.18/19.20  ----------------------
% 32.18/19.20  #Subsume      : 3600
% 32.18/19.20  #Demod        : 929
% 32.18/19.20  #Tautology    : 362
% 32.18/19.20  #SimpNegUnit  : 249
% 32.18/19.20  #BackRed      : 21
% 32.18/19.20  
% 32.18/19.20  #Partial instantiations: 0
% 32.18/19.20  #Strategies tried      : 1
% 32.18/19.20  
% 32.18/19.20  Timing (in seconds)
% 32.18/19.20  ----------------------
% 32.18/19.20  Preprocessing        : 0.53
% 32.18/19.20  Parsing              : 0.26
% 32.18/19.20  CNF conversion       : 0.04
% 32.18/19.20  Main loop            : 17.80
% 32.18/19.20  Inferencing          : 2.26
% 32.18/19.20  Reduction            : 6.11
% 32.18/19.20  Demodulation         : 2.06
% 32.18/19.20  BG Simplification    : 0.28
% 32.18/19.20  Subsumption          : 8.03
% 32.18/19.20  Abstraction          : 0.36
% 32.18/19.20  MUC search           : 0.00
% 32.18/19.20  Cooper               : 0.00
% 32.18/19.20  Total                : 18.37
% 32.18/19.20  Index Insertion      : 0.00
% 32.18/19.20  Index Deletion       : 0.00
% 32.18/19.20  Index Matching       : 0.00
% 32.18/19.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
