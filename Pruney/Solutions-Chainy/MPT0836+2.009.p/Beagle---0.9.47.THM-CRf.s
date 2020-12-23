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
% DateTime   : Thu Dec  3 10:08:03 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 275 expanded)
%              Number of leaves         :   42 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  194 ( 637 expanded)
%              Number of equality atoms :   29 (  68 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => ( r2_hidden(D,k1_relset_1(A,B,C))
                    <=> ? [E] :
                          ( m1_subset_1(E,B)
                          & r2_hidden(k4_tarski(D,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_52,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_928,plain,(
    ! [A_243,B_244,C_245] :
      ( k1_relset_1(A_243,B_244,C_245) = k1_relat_1(C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_932,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_928])).

tff(c_330,plain,(
    ! [A_146,B_147,C_148] :
      ( k1_relset_1(A_146,B_147,C_148) = k1_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_334,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_330])).

tff(c_66,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_88,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_62,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_123,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_128,plain,(
    ! [C_110,A_111,D_112] :
      ( r2_hidden(C_110,k1_relat_1(A_111))
      | ~ r2_hidden(k4_tarski(C_110,D_112),A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_132,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_123,c_128])).

tff(c_240,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_244,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_240])).

tff(c_56,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_89),'#skF_8')
      | ~ m1_subset_1(E_89,'#skF_7')
      | ~ r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_268,plain,(
    ! [E_133] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_133),'#skF_8')
      | ~ m1_subset_1(E_133,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_244,c_56])).

tff(c_271,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_123,c_268])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_271])).

tff(c_276,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_336,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_276])).

tff(c_24,plain,(
    ! [A_28,B_29] : v1_relat_1(k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_89,plain,(
    ! [B_97,A_98] :
      ( v1_relat_1(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_98))
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_92,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_50,c_89])).

tff(c_95,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_92])).

tff(c_283,plain,(
    ! [C_137,B_138,A_139] :
      ( v5_relat_1(C_137,B_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_287,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_283])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_288,plain,(
    ! [B_140,A_141] :
      ( k5_relat_1(B_140,k6_relat_1(A_141)) = B_140
      | ~ r1_tarski(k2_relat_1(B_140),A_141)
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_295,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_288])).

tff(c_22,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ! [A_39] : k1_relat_1(k6_relat_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_346,plain,(
    ! [A_149,B_150] :
      ( k10_relat_1(A_149,k1_relat_1(B_150)) = k1_relat_1(k5_relat_1(A_149,B_150))
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_355,plain,(
    ! [A_149,A_39] :
      ( k1_relat_1(k5_relat_1(A_149,k6_relat_1(A_39))) = k10_relat_1(A_149,A_39)
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_346])).

tff(c_365,plain,(
    ! [A_153,A_154] :
      ( k1_relat_1(k5_relat_1(A_153,k6_relat_1(A_154))) = k10_relat_1(A_153,A_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_355])).

tff(c_406,plain,(
    ! [B_157,A_158] :
      ( k10_relat_1(B_157,A_158) = k1_relat_1(B_157)
      | ~ v1_relat_1(B_157)
      | ~ v5_relat_1(B_157,A_158)
      | ~ v1_relat_1(B_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_365])).

tff(c_409,plain,
    ( k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_287,c_406])).

tff(c_415,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_409])).

tff(c_460,plain,(
    ! [A_162,B_163,C_164] :
      ( r2_hidden('#skF_5'(A_162,B_163,C_164),B_163)
      | ~ r2_hidden(A_162,k10_relat_1(C_164,B_163))
      | ~ v1_relat_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_544,plain,(
    ! [A_174,B_175,C_176] :
      ( m1_subset_1('#skF_5'(A_174,B_175,C_176),B_175)
      | ~ r2_hidden(A_174,k10_relat_1(C_176,B_175))
      | ~ v1_relat_1(C_176) ) ),
    inference(resolution,[status(thm)],[c_460,c_2])).

tff(c_552,plain,(
    ! [A_174] :
      ( m1_subset_1('#skF_5'(A_174,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_174,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_544])).

tff(c_567,plain,(
    ! [A_177] :
      ( m1_subset_1('#skF_5'(A_177,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_177,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_552])).

tff(c_586,plain,(
    m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_336,c_567])).

tff(c_677,plain,(
    ! [A_202,B_203,C_204] :
      ( r2_hidden(k4_tarski(A_202,'#skF_5'(A_202,B_203,C_204)),C_204)
      | ~ r2_hidden(A_202,k10_relat_1(C_204,B_203))
      | ~ v1_relat_1(C_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_277,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_89),'#skF_8')
      | ~ m1_subset_1(E_89,'#skF_7')
      | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_419,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_89),'#skF_8')
      | ~ m1_subset_1(E_89,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_60])).

tff(c_691,plain,(
    ! [B_203] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_203,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_203))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_677,c_419])).

tff(c_772,plain,(
    ! [B_210] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_210,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_210)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_691])).

tff(c_775,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_772])).

tff(c_782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_586,c_775])).

tff(c_783,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_934,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_783])).

tff(c_790,plain,(
    ! [B_211,A_212] :
      ( v1_relat_1(B_211)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(A_212))
      | ~ v1_relat_1(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_793,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_50,c_790])).

tff(c_796,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_793])).

tff(c_804,plain,(
    ! [C_217,B_218,A_219] :
      ( v5_relat_1(C_217,B_218)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_219,B_218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_808,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_804])).

tff(c_832,plain,(
    ! [B_231,A_232] :
      ( k5_relat_1(B_231,k6_relat_1(A_232)) = B_231
      | ~ r1_tarski(k2_relat_1(B_231),A_232)
      | ~ v1_relat_1(B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_839,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_832])).

tff(c_851,plain,(
    ! [A_235,B_236] :
      ( k10_relat_1(A_235,k1_relat_1(B_236)) = k1_relat_1(k5_relat_1(A_235,B_236))
      | ~ v1_relat_1(B_236)
      | ~ v1_relat_1(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_860,plain,(
    ! [A_235,A_39] :
      ( k1_relat_1(k5_relat_1(A_235,k6_relat_1(A_39))) = k10_relat_1(A_235,A_39)
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(A_235) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_851])).

tff(c_887,plain,(
    ! [A_239,A_240] :
      ( k1_relat_1(k5_relat_1(A_239,k6_relat_1(A_240))) = k10_relat_1(A_239,A_240)
      | ~ v1_relat_1(A_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_860])).

tff(c_944,plain,(
    ! [B_246,A_247] :
      ( k10_relat_1(B_246,A_247) = k1_relat_1(B_246)
      | ~ v1_relat_1(B_246)
      | ~ v5_relat_1(B_246,A_247)
      | ~ v1_relat_1(B_246) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_887])).

tff(c_947,plain,
    ( k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_808,c_944])).

tff(c_953,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_947])).

tff(c_957,plain,(
    ! [A_248,B_249,C_250] :
      ( r2_hidden('#skF_5'(A_248,B_249,C_250),B_249)
      | ~ r2_hidden(A_248,k10_relat_1(C_250,B_249))
      | ~ v1_relat_1(C_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1034,plain,(
    ! [A_257,B_258,C_259] :
      ( m1_subset_1('#skF_5'(A_257,B_258,C_259),B_258)
      | ~ r2_hidden(A_257,k10_relat_1(C_259,B_258))
      | ~ v1_relat_1(C_259) ) ),
    inference(resolution,[status(thm)],[c_957,c_2])).

tff(c_1042,plain,(
    ! [A_257] :
      ( m1_subset_1('#skF_5'(A_257,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_257,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_1034])).

tff(c_1057,plain,(
    ! [A_260] :
      ( m1_subset_1('#skF_5'(A_260,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_260,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_1042])).

tff(c_1076,plain,(
    m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_934,c_1057])).

tff(c_1169,plain,(
    ! [A_280,B_281,C_282] :
      ( r2_hidden(k4_tarski(A_280,'#skF_5'(A_280,B_281,C_282)),C_282)
      | ~ r2_hidden(A_280,k10_relat_1(C_282,B_281))
      | ~ v1_relat_1(C_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_784,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_89),'#skF_8')
      | ~ m1_subset_1(E_89,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_815,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_89),'#skF_8')
      | ~ m1_subset_1(E_89,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_784,c_64])).

tff(c_1183,plain,(
    ! [B_281] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_281,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_281))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1169,c_815])).

tff(c_1198,plain,(
    ! [B_283] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_283,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_283)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_1183])).

tff(c_1201,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_1198])).

tff(c_1208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_1076,c_1201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:44:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.57  
% 3.54/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.57  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 3.54/1.57  
% 3.54/1.57  %Foreground sorts:
% 3.54/1.57  
% 3.54/1.57  
% 3.54/1.57  %Background operators:
% 3.54/1.57  
% 3.54/1.57  
% 3.54/1.57  %Foreground operators:
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.54/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.54/1.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.54/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.54/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.54/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.57  tff('#skF_10', type, '#skF_10': $i).
% 3.54/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.54/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.57  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.54/1.57  tff('#skF_9', type, '#skF_9': $i).
% 3.54/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.54/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.54/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.54/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.54/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.54/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.54/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.54/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.54/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.57  
% 3.61/1.59  tff(f_113, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relset_1)).
% 3.61/1.59  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.61/1.59  tff(f_50, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.61/1.59  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.61/1.59  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.61/1.59  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.61/1.59  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.61/1.59  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.61/1.59  tff(f_52, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.61/1.59  tff(f_76, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.61/1.59  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.61/1.59  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.61/1.59  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.61/1.59  tff(c_50, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.61/1.59  tff(c_928, plain, (![A_243, B_244, C_245]: (k1_relset_1(A_243, B_244, C_245)=k1_relat_1(C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.61/1.59  tff(c_932, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_928])).
% 3.61/1.59  tff(c_330, plain, (![A_146, B_147, C_148]: (k1_relset_1(A_146, B_147, C_148)=k1_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.61/1.59  tff(c_334, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_330])).
% 3.61/1.59  tff(c_66, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | m1_subset_1('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.61/1.59  tff(c_88, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_66])).
% 3.61/1.59  tff(c_62, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.61/1.59  tff(c_123, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_62])).
% 3.61/1.59  tff(c_128, plain, (![C_110, A_111, D_112]: (r2_hidden(C_110, k1_relat_1(A_111)) | ~r2_hidden(k4_tarski(C_110, D_112), A_111))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.61/1.59  tff(c_132, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_123, c_128])).
% 3.61/1.59  tff(c_240, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.61/1.59  tff(c_244, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_240])).
% 3.61/1.59  tff(c_56, plain, (![E_89]: (~r2_hidden(k4_tarski('#skF_9', E_89), '#skF_8') | ~m1_subset_1(E_89, '#skF_7') | ~r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.61/1.59  tff(c_268, plain, (![E_133]: (~r2_hidden(k4_tarski('#skF_9', E_133), '#skF_8') | ~m1_subset_1(E_133, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_244, c_56])).
% 3.61/1.59  tff(c_271, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_123, c_268])).
% 3.61/1.59  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_271])).
% 3.61/1.59  tff(c_276, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_62])).
% 3.61/1.59  tff(c_336, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_276])).
% 3.61/1.59  tff(c_24, plain, (![A_28, B_29]: (v1_relat_1(k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.61/1.59  tff(c_89, plain, (![B_97, A_98]: (v1_relat_1(B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_98)) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.61/1.59  tff(c_92, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_50, c_89])).
% 3.61/1.59  tff(c_95, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_92])).
% 3.61/1.59  tff(c_283, plain, (![C_137, B_138, A_139]: (v5_relat_1(C_137, B_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.61/1.59  tff(c_287, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_50, c_283])).
% 3.61/1.59  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.61/1.59  tff(c_288, plain, (![B_140, A_141]: (k5_relat_1(B_140, k6_relat_1(A_141))=B_140 | ~r1_tarski(k2_relat_1(B_140), A_141) | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.61/1.59  tff(c_295, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_8, c_288])).
% 3.61/1.59  tff(c_22, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.61/1.59  tff(c_36, plain, (![A_39]: (k1_relat_1(k6_relat_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.61/1.59  tff(c_346, plain, (![A_149, B_150]: (k10_relat_1(A_149, k1_relat_1(B_150))=k1_relat_1(k5_relat_1(A_149, B_150)) | ~v1_relat_1(B_150) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.61/1.59  tff(c_355, plain, (![A_149, A_39]: (k1_relat_1(k5_relat_1(A_149, k6_relat_1(A_39)))=k10_relat_1(A_149, A_39) | ~v1_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_36, c_346])).
% 3.61/1.59  tff(c_365, plain, (![A_153, A_154]: (k1_relat_1(k5_relat_1(A_153, k6_relat_1(A_154)))=k10_relat_1(A_153, A_154) | ~v1_relat_1(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_355])).
% 3.61/1.59  tff(c_406, plain, (![B_157, A_158]: (k10_relat_1(B_157, A_158)=k1_relat_1(B_157) | ~v1_relat_1(B_157) | ~v5_relat_1(B_157, A_158) | ~v1_relat_1(B_157))), inference(superposition, [status(thm), theory('equality')], [c_295, c_365])).
% 3.61/1.59  tff(c_409, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_287, c_406])).
% 3.61/1.59  tff(c_415, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_409])).
% 3.61/1.59  tff(c_460, plain, (![A_162, B_163, C_164]: (r2_hidden('#skF_5'(A_162, B_163, C_164), B_163) | ~r2_hidden(A_162, k10_relat_1(C_164, B_163)) | ~v1_relat_1(C_164))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.61/1.59  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.61/1.59  tff(c_544, plain, (![A_174, B_175, C_176]: (m1_subset_1('#skF_5'(A_174, B_175, C_176), B_175) | ~r2_hidden(A_174, k10_relat_1(C_176, B_175)) | ~v1_relat_1(C_176))), inference(resolution, [status(thm)], [c_460, c_2])).
% 3.61/1.59  tff(c_552, plain, (![A_174]: (m1_subset_1('#skF_5'(A_174, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_174, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_415, c_544])).
% 3.61/1.59  tff(c_567, plain, (![A_177]: (m1_subset_1('#skF_5'(A_177, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_177, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_552])).
% 3.61/1.59  tff(c_586, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_336, c_567])).
% 3.61/1.59  tff(c_677, plain, (![A_202, B_203, C_204]: (r2_hidden(k4_tarski(A_202, '#skF_5'(A_202, B_203, C_204)), C_204) | ~r2_hidden(A_202, k10_relat_1(C_204, B_203)) | ~v1_relat_1(C_204))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.61/1.59  tff(c_277, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_62])).
% 3.61/1.59  tff(c_60, plain, (![E_89]: (~r2_hidden(k4_tarski('#skF_9', E_89), '#skF_8') | ~m1_subset_1(E_89, '#skF_7') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.61/1.59  tff(c_419, plain, (![E_89]: (~r2_hidden(k4_tarski('#skF_9', E_89), '#skF_8') | ~m1_subset_1(E_89, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_277, c_60])).
% 3.61/1.59  tff(c_691, plain, (![B_203]: (~m1_subset_1('#skF_5'('#skF_9', B_203, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_203)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_677, c_419])).
% 3.61/1.59  tff(c_772, plain, (![B_210]: (~m1_subset_1('#skF_5'('#skF_9', B_210, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_210)))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_691])).
% 3.61/1.59  tff(c_775, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_415, c_772])).
% 3.61/1.59  tff(c_782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_336, c_586, c_775])).
% 3.61/1.59  tff(c_783, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_66])).
% 3.61/1.59  tff(c_934, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_932, c_783])).
% 3.61/1.59  tff(c_790, plain, (![B_211, A_212]: (v1_relat_1(B_211) | ~m1_subset_1(B_211, k1_zfmisc_1(A_212)) | ~v1_relat_1(A_212))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.61/1.59  tff(c_793, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_50, c_790])).
% 3.61/1.59  tff(c_796, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_793])).
% 3.61/1.59  tff(c_804, plain, (![C_217, B_218, A_219]: (v5_relat_1(C_217, B_218) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_219, B_218))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.61/1.59  tff(c_808, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_50, c_804])).
% 3.61/1.59  tff(c_832, plain, (![B_231, A_232]: (k5_relat_1(B_231, k6_relat_1(A_232))=B_231 | ~r1_tarski(k2_relat_1(B_231), A_232) | ~v1_relat_1(B_231))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.61/1.59  tff(c_839, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_8, c_832])).
% 3.61/1.59  tff(c_851, plain, (![A_235, B_236]: (k10_relat_1(A_235, k1_relat_1(B_236))=k1_relat_1(k5_relat_1(A_235, B_236)) | ~v1_relat_1(B_236) | ~v1_relat_1(A_235))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.61/1.59  tff(c_860, plain, (![A_235, A_39]: (k1_relat_1(k5_relat_1(A_235, k6_relat_1(A_39)))=k10_relat_1(A_235, A_39) | ~v1_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(A_235))), inference(superposition, [status(thm), theory('equality')], [c_36, c_851])).
% 3.61/1.59  tff(c_887, plain, (![A_239, A_240]: (k1_relat_1(k5_relat_1(A_239, k6_relat_1(A_240)))=k10_relat_1(A_239, A_240) | ~v1_relat_1(A_239))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_860])).
% 3.61/1.59  tff(c_944, plain, (![B_246, A_247]: (k10_relat_1(B_246, A_247)=k1_relat_1(B_246) | ~v1_relat_1(B_246) | ~v5_relat_1(B_246, A_247) | ~v1_relat_1(B_246))), inference(superposition, [status(thm), theory('equality')], [c_839, c_887])).
% 3.61/1.59  tff(c_947, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_808, c_944])).
% 3.61/1.59  tff(c_953, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_947])).
% 3.61/1.59  tff(c_957, plain, (![A_248, B_249, C_250]: (r2_hidden('#skF_5'(A_248, B_249, C_250), B_249) | ~r2_hidden(A_248, k10_relat_1(C_250, B_249)) | ~v1_relat_1(C_250))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.61/1.59  tff(c_1034, plain, (![A_257, B_258, C_259]: (m1_subset_1('#skF_5'(A_257, B_258, C_259), B_258) | ~r2_hidden(A_257, k10_relat_1(C_259, B_258)) | ~v1_relat_1(C_259))), inference(resolution, [status(thm)], [c_957, c_2])).
% 3.61/1.59  tff(c_1042, plain, (![A_257]: (m1_subset_1('#skF_5'(A_257, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_257, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_953, c_1034])).
% 3.61/1.59  tff(c_1057, plain, (![A_260]: (m1_subset_1('#skF_5'(A_260, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_260, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_796, c_1042])).
% 3.61/1.59  tff(c_1076, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_934, c_1057])).
% 3.61/1.59  tff(c_1169, plain, (![A_280, B_281, C_282]: (r2_hidden(k4_tarski(A_280, '#skF_5'(A_280, B_281, C_282)), C_282) | ~r2_hidden(A_280, k10_relat_1(C_282, B_281)) | ~v1_relat_1(C_282))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.61/1.59  tff(c_784, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_66])).
% 3.61/1.59  tff(c_64, plain, (![E_89]: (~r2_hidden(k4_tarski('#skF_9', E_89), '#skF_8') | ~m1_subset_1(E_89, '#skF_7') | m1_subset_1('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.61/1.59  tff(c_815, plain, (![E_89]: (~r2_hidden(k4_tarski('#skF_9', E_89), '#skF_8') | ~m1_subset_1(E_89, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_784, c_64])).
% 3.61/1.59  tff(c_1183, plain, (![B_281]: (~m1_subset_1('#skF_5'('#skF_9', B_281, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_281)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1169, c_815])).
% 3.61/1.59  tff(c_1198, plain, (![B_283]: (~m1_subset_1('#skF_5'('#skF_9', B_283, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_283)))), inference(demodulation, [status(thm), theory('equality')], [c_796, c_1183])).
% 3.61/1.59  tff(c_1201, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_953, c_1198])).
% 3.61/1.59  tff(c_1208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_934, c_1076, c_1201])).
% 3.61/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.59  
% 3.61/1.59  Inference rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Ref     : 0
% 3.61/1.59  #Sup     : 237
% 3.61/1.59  #Fact    : 0
% 3.61/1.59  #Define  : 0
% 3.61/1.59  #Split   : 2
% 3.61/1.59  #Chain   : 0
% 3.61/1.59  #Close   : 0
% 3.61/1.59  
% 3.61/1.59  Ordering : KBO
% 3.61/1.59  
% 3.61/1.59  Simplification rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Subsume      : 15
% 3.61/1.59  #Demod        : 108
% 3.61/1.59  #Tautology    : 77
% 3.61/1.59  #SimpNegUnit  : 2
% 3.61/1.59  #BackRed      : 4
% 3.61/1.59  
% 3.61/1.59  #Partial instantiations: 0
% 3.61/1.60  #Strategies tried      : 1
% 3.61/1.60  
% 3.61/1.60  Timing (in seconds)
% 3.61/1.60  ----------------------
% 3.61/1.60  Preprocessing        : 0.35
% 3.61/1.60  Parsing              : 0.18
% 3.61/1.60  CNF conversion       : 0.03
% 3.61/1.60  Main loop            : 0.46
% 3.61/1.60  Inferencing          : 0.18
% 3.61/1.60  Reduction            : 0.14
% 3.61/1.60  Demodulation         : 0.10
% 3.61/1.60  BG Simplification    : 0.03
% 3.61/1.60  Subsumption          : 0.07
% 3.61/1.60  Abstraction          : 0.03
% 3.61/1.60  MUC search           : 0.00
% 3.61/1.60  Cooper               : 0.00
% 3.61/1.60  Total                : 0.86
% 3.61/1.60  Index Insertion      : 0.00
% 3.61/1.60  Index Deletion       : 0.00
% 3.61/1.60  Index Matching       : 0.00
% 3.61/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
