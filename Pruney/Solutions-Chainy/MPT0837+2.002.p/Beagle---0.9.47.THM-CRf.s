%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:05 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 283 expanded)
%              Number of leaves         :   39 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 630 expanded)
%              Number of equality atoms :   14 (  55 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2574,plain,(
    ! [A_517,B_518,C_519] :
      ( k2_relset_1(A_517,B_518,C_519) = k2_relat_1(C_519)
      | ~ m1_subset_1(C_519,k1_zfmisc_1(k2_zfmisc_1(A_517,B_518))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2593,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_2574])).

tff(c_794,plain,(
    ! [A_252,B_253,C_254] :
      ( k2_relset_1(A_252,B_253,C_254) = k2_relat_1(C_254)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_808,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_794])).

tff(c_64,plain,
    ( m1_subset_1('#skF_7','#skF_4')
    | r2_hidden('#skF_8',k2_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_88,plain,(
    r2_hidden('#skF_8',k2_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_811,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_88])).

tff(c_94,plain,(
    ! [C_92,A_93,B_94] :
      ( v1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_103,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_94])).

tff(c_639,plain,(
    ! [C_216,A_217,B_218] :
      ( v4_relat_1(C_216,A_217)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_653,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_639])).

tff(c_36,plain,(
    ! [B_25,A_24] :
      ( k7_relat_1(B_25,A_24) = B_25
      | ~ v4_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_656,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_653,c_36])).

tff(c_659,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_656])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_672,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_659,c_34])).

tff(c_676,plain,(
    k9_relat_1('#skF_5','#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_672])).

tff(c_1754,plain,(
    ! [A_403,B_404,C_405] :
      ( r2_hidden(k4_tarski('#skF_2'(A_403,B_404,C_405),A_403),C_405)
      | ~ r2_hidden(A_403,k9_relat_1(C_405,B_404))
      | ~ v1_relat_1(C_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    ! [E_80] :
      ( ~ r2_hidden('#skF_6',k2_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ r2_hidden(k4_tarski(E_80,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(E_80,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1192,plain,(
    ! [E_80] :
      ( ~ r2_hidden('#skF_6',k2_relat_1('#skF_5'))
      | ~ r2_hidden(k4_tarski(E_80,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(E_80,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_54])).

tff(c_1193,plain,(
    ~ r2_hidden('#skF_6',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1192])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1505,plain,(
    ! [D_372,C_373,B_374,A_375] :
      ( m1_subset_1(D_372,k1_zfmisc_1(k2_zfmisc_1(C_373,B_374)))
      | ~ r1_tarski(k2_relat_1(D_372),B_374)
      | ~ m1_subset_1(D_372,k1_zfmisc_1(k2_zfmisc_1(C_373,A_375))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1521,plain,(
    ! [B_376] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_376)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_376) ) ),
    inference(resolution,[status(thm)],[c_48,c_1505])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1553,plain,(
    ! [B_378] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_4',B_378))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_378) ) ),
    inference(resolution,[status(thm)],[c_1521,c_22])).

tff(c_1558,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_4',k2_relat_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_12,c_1553])).

tff(c_924,plain,(
    ! [A_272,B_273,C_274] :
      ( r2_hidden('#skF_2'(A_272,B_273,C_274),B_273)
      | ~ r2_hidden(A_272,k9_relat_1(C_274,B_273))
      | ~ v1_relat_1(C_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_934,plain,(
    ! [A_279,B_280,C_281] :
      ( m1_subset_1('#skF_2'(A_279,B_280,C_281),B_280)
      | ~ r2_hidden(A_279,k9_relat_1(C_281,B_280))
      | ~ v1_relat_1(C_281) ) ),
    inference(resolution,[status(thm)],[c_924,c_20])).

tff(c_944,plain,(
    ! [A_279] :
      ( m1_subset_1('#skF_2'(A_279,'#skF_4','#skF_5'),'#skF_4')
      | ~ r2_hidden(A_279,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_934])).

tff(c_955,plain,(
    ! [A_282] :
      ( m1_subset_1('#skF_2'(A_282,'#skF_4','#skF_5'),'#skF_4')
      | ~ r2_hidden(A_282,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_944])).

tff(c_972,plain,(
    m1_subset_1('#skF_2'('#skF_8','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_811,c_955])).

tff(c_1031,plain,(
    ! [A_309,B_310,C_311] :
      ( r2_hidden(k4_tarski('#skF_2'(A_309,B_310,C_311),A_309),C_311)
      | ~ r2_hidden(A_309,k9_relat_1(C_311,B_310))
      | ~ v1_relat_1(C_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,(
    ! [E_80] :
      ( r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5')
      | ~ r2_hidden(k4_tarski(E_80,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(E_80,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_824,plain,(
    ! [E_80] :
      ( ~ r2_hidden(k4_tarski(E_80,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(E_80,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_1042,plain,(
    ! [B_310] :
      ( ~ m1_subset_1('#skF_2'('#skF_8',B_310,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_8',k9_relat_1('#skF_5',B_310))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1031,c_824])).

tff(c_1115,plain,(
    ! [B_315] :
      ( ~ m1_subset_1('#skF_2'('#skF_8',B_315,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_8',k9_relat_1('#skF_5',B_315)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1042])).

tff(c_1118,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_8','#skF_4','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_8',k2_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_1115])).

tff(c_1121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_972,c_1118])).

tff(c_1122,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1137,plain,(
    ! [B_317] :
      ( r2_hidden(k4_tarski('#skF_7','#skF_6'),B_317)
      | ~ r1_tarski('#skF_5',B_317) ) ),
    inference(resolution,[status(thm)],[c_1122,c_2])).

tff(c_16,plain,(
    ! [B_9,D_11,A_8,C_10] :
      ( r2_hidden(B_9,D_11)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1152,plain,(
    ! [D_11,C_10] :
      ( r2_hidden('#skF_6',D_11)
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(C_10,D_11)) ) ),
    inference(resolution,[status(thm)],[c_1137,c_16])).

tff(c_1567,plain,(
    r2_hidden('#skF_6',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1558,c_1152])).

tff(c_1590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1193,c_1567])).

tff(c_1591,plain,(
    ! [E_80] :
      ( ~ r2_hidden(k4_tarski(E_80,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(E_80,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1192])).

tff(c_1758,plain,(
    ! [B_404] :
      ( ~ m1_subset_1('#skF_2'('#skF_8',B_404,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_8',k9_relat_1('#skF_5',B_404))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1754,c_1591])).

tff(c_2173,plain,(
    ! [B_450] :
      ( ~ m1_subset_1('#skF_2'('#skF_8',B_450,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_8',k9_relat_1('#skF_5',B_450)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1758])).

tff(c_2176,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_8','#skF_4','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_8',k2_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_2173])).

tff(c_2178,plain,(
    ~ m1_subset_1('#skF_2'('#skF_8','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_2176])).

tff(c_1614,plain,(
    ! [A_381,B_382,C_383] :
      ( r2_hidden('#skF_2'(A_381,B_382,C_383),B_382)
      | ~ r2_hidden(A_381,k9_relat_1(C_383,B_382))
      | ~ v1_relat_1(C_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2179,plain,(
    ! [A_451,B_452,C_453] :
      ( m1_subset_1('#skF_2'(A_451,B_452,C_453),B_452)
      | ~ r2_hidden(A_451,k9_relat_1(C_453,B_452))
      | ~ v1_relat_1(C_453) ) ),
    inference(resolution,[status(thm)],[c_1614,c_20])).

tff(c_2204,plain,(
    ! [A_451] :
      ( m1_subset_1('#skF_2'(A_451,'#skF_4','#skF_5'),'#skF_4')
      | ~ r2_hidden(A_451,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_2179])).

tff(c_2220,plain,(
    ! [A_454] :
      ( m1_subset_1('#skF_2'(A_454,'#skF_4','#skF_5'),'#skF_4')
      | ~ r2_hidden(A_454,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_2204])).

tff(c_2250,plain,(
    m1_subset_1('#skF_2'('#skF_8','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_811,c_2220])).

tff(c_2269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2178,c_2250])).

tff(c_2271,plain,(
    ~ r2_hidden('#skF_8',k2_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_6',k2_relset_1('#skF_4','#skF_3','#skF_5'))
    | r2_hidden('#skF_8',k2_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2394,plain,(
    ~ r2_hidden('#skF_6',k2_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_2271,c_60])).

tff(c_2595,plain,(
    ~ r2_hidden('#skF_6',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2593,c_2394])).

tff(c_3015,plain,(
    ! [D_586,C_587,B_588,A_589] :
      ( m1_subset_1(D_586,k1_zfmisc_1(k2_zfmisc_1(C_587,B_588)))
      | ~ r1_tarski(k2_relat_1(D_586),B_588)
      | ~ m1_subset_1(D_586,k1_zfmisc_1(k2_zfmisc_1(C_587,A_589))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3035,plain,(
    ! [B_590] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_590)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_590) ) ),
    inference(resolution,[status(thm)],[c_48,c_3015])).

tff(c_3067,plain,(
    ! [B_592] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_4',B_592))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_592) ) ),
    inference(resolution,[status(thm)],[c_3035,c_22])).

tff(c_3072,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_4',k2_relat_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_12,c_3067])).

tff(c_62,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5')
    | r2_hidden('#skF_8',k2_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2334,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2271,c_62])).

tff(c_2366,plain,(
    ! [C_482,B_483,A_484] :
      ( r2_hidden(C_482,B_483)
      | ~ r2_hidden(C_482,A_484)
      | ~ r1_tarski(A_484,B_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2371,plain,(
    ! [B_483] :
      ( r2_hidden(k4_tarski('#skF_7','#skF_6'),B_483)
      | ~ r1_tarski('#skF_5',B_483) ) ),
    inference(resolution,[status(thm)],[c_2334,c_2366])).

tff(c_2518,plain,(
    ! [B_505,D_506,A_507,C_508] :
      ( r2_hidden(B_505,D_506)
      | ~ r2_hidden(k4_tarski(A_507,B_505),k2_zfmisc_1(C_508,D_506)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2523,plain,(
    ! [D_506,C_508] :
      ( r2_hidden('#skF_6',D_506)
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(C_508,D_506)) ) ),
    inference(resolution,[status(thm)],[c_2371,c_2518])).

tff(c_3084,plain,(
    r2_hidden('#skF_6',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3072,c_2523])).

tff(c_3108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2595,c_3084])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:38:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.88  
% 4.87/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.88  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4 > #skF_1
% 4.87/1.88  
% 4.87/1.88  %Foreground sorts:
% 4.87/1.88  
% 4.87/1.88  
% 4.87/1.88  %Background operators:
% 4.87/1.88  
% 4.87/1.88  
% 4.87/1.88  %Foreground operators:
% 4.87/1.88  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.87/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.87/1.88  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.87/1.88  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.87/1.88  tff('#skF_7', type, '#skF_7': $i).
% 4.87/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.87/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.87/1.88  tff('#skF_6', type, '#skF_6': $i).
% 4.87/1.88  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.87/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.87/1.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.87/1.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.87/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.87/1.88  tff('#skF_8', type, '#skF_8': $i).
% 4.87/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.87/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.87/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.87/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/1.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.87/1.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.87/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.87/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.87/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.87/1.88  
% 4.87/1.90  tff(f_112, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 4.87/1.90  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.87/1.90  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.87/1.90  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.87/1.90  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.87/1.90  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.87/1.90  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.87/1.90  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.87/1.90  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 4.87/1.90  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.87/1.90  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.87/1.90  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.87/1.90  tff(f_44, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.87/1.90  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.87/1.90  tff(c_2574, plain, (![A_517, B_518, C_519]: (k2_relset_1(A_517, B_518, C_519)=k2_relat_1(C_519) | ~m1_subset_1(C_519, k1_zfmisc_1(k2_zfmisc_1(A_517, B_518))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.87/1.90  tff(c_2593, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_2574])).
% 4.87/1.90  tff(c_794, plain, (![A_252, B_253, C_254]: (k2_relset_1(A_252, B_253, C_254)=k2_relat_1(C_254) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.87/1.90  tff(c_808, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_794])).
% 4.87/1.90  tff(c_64, plain, (m1_subset_1('#skF_7', '#skF_4') | r2_hidden('#skF_8', k2_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.87/1.90  tff(c_88, plain, (r2_hidden('#skF_8', k2_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_64])).
% 4.87/1.90  tff(c_811, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_88])).
% 4.87/1.90  tff(c_94, plain, (![C_92, A_93, B_94]: (v1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.87/1.90  tff(c_103, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_94])).
% 4.87/1.90  tff(c_639, plain, (![C_216, A_217, B_218]: (v4_relat_1(C_216, A_217) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.87/1.90  tff(c_653, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_639])).
% 4.87/1.90  tff(c_36, plain, (![B_25, A_24]: (k7_relat_1(B_25, A_24)=B_25 | ~v4_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.87/1.90  tff(c_656, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_653, c_36])).
% 4.87/1.90  tff(c_659, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_656])).
% 4.87/1.90  tff(c_34, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.87/1.90  tff(c_672, plain, (k9_relat_1('#skF_5', '#skF_4')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_659, c_34])).
% 4.87/1.90  tff(c_676, plain, (k9_relat_1('#skF_5', '#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_672])).
% 4.87/1.90  tff(c_1754, plain, (![A_403, B_404, C_405]: (r2_hidden(k4_tarski('#skF_2'(A_403, B_404, C_405), A_403), C_405) | ~r2_hidden(A_403, k9_relat_1(C_405, B_404)) | ~v1_relat_1(C_405))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.87/1.90  tff(c_54, plain, (![E_80]: (~r2_hidden('#skF_6', k2_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~r2_hidden(k4_tarski(E_80, '#skF_8'), '#skF_5') | ~m1_subset_1(E_80, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.87/1.90  tff(c_1192, plain, (![E_80]: (~r2_hidden('#skF_6', k2_relat_1('#skF_5')) | ~r2_hidden(k4_tarski(E_80, '#skF_8'), '#skF_5') | ~m1_subset_1(E_80, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_54])).
% 4.87/1.90  tff(c_1193, plain, (~r2_hidden('#skF_6', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1192])).
% 4.87/1.90  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.87/1.90  tff(c_1505, plain, (![D_372, C_373, B_374, A_375]: (m1_subset_1(D_372, k1_zfmisc_1(k2_zfmisc_1(C_373, B_374))) | ~r1_tarski(k2_relat_1(D_372), B_374) | ~m1_subset_1(D_372, k1_zfmisc_1(k2_zfmisc_1(C_373, A_375))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.87/1.90  tff(c_1521, plain, (![B_376]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_376))) | ~r1_tarski(k2_relat_1('#skF_5'), B_376))), inference(resolution, [status(thm)], [c_48, c_1505])).
% 4.87/1.90  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.87/1.90  tff(c_1553, plain, (![B_378]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_4', B_378)) | ~r1_tarski(k2_relat_1('#skF_5'), B_378))), inference(resolution, [status(thm)], [c_1521, c_22])).
% 4.87/1.90  tff(c_1558, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_4', k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_1553])).
% 4.87/1.90  tff(c_924, plain, (![A_272, B_273, C_274]: (r2_hidden('#skF_2'(A_272, B_273, C_274), B_273) | ~r2_hidden(A_272, k9_relat_1(C_274, B_273)) | ~v1_relat_1(C_274))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.87/1.90  tff(c_20, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.87/1.90  tff(c_934, plain, (![A_279, B_280, C_281]: (m1_subset_1('#skF_2'(A_279, B_280, C_281), B_280) | ~r2_hidden(A_279, k9_relat_1(C_281, B_280)) | ~v1_relat_1(C_281))), inference(resolution, [status(thm)], [c_924, c_20])).
% 4.87/1.90  tff(c_944, plain, (![A_279]: (m1_subset_1('#skF_2'(A_279, '#skF_4', '#skF_5'), '#skF_4') | ~r2_hidden(A_279, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_676, c_934])).
% 4.87/1.90  tff(c_955, plain, (![A_282]: (m1_subset_1('#skF_2'(A_282, '#skF_4', '#skF_5'), '#skF_4') | ~r2_hidden(A_282, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_944])).
% 4.87/1.90  tff(c_972, plain, (m1_subset_1('#skF_2'('#skF_8', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_811, c_955])).
% 4.87/1.90  tff(c_1031, plain, (![A_309, B_310, C_311]: (r2_hidden(k4_tarski('#skF_2'(A_309, B_310, C_311), A_309), C_311) | ~r2_hidden(A_309, k9_relat_1(C_311, B_310)) | ~v1_relat_1(C_311))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.87/1.90  tff(c_56, plain, (![E_80]: (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden(k4_tarski(E_80, '#skF_8'), '#skF_5') | ~m1_subset_1(E_80, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.87/1.90  tff(c_824, plain, (![E_80]: (~r2_hidden(k4_tarski(E_80, '#skF_8'), '#skF_5') | ~m1_subset_1(E_80, '#skF_4'))), inference(splitLeft, [status(thm)], [c_56])).
% 4.87/1.90  tff(c_1042, plain, (![B_310]: (~m1_subset_1('#skF_2'('#skF_8', B_310, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_8', k9_relat_1('#skF_5', B_310)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1031, c_824])).
% 4.87/1.90  tff(c_1115, plain, (![B_315]: (~m1_subset_1('#skF_2'('#skF_8', B_315, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_8', k9_relat_1('#skF_5', B_315)))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1042])).
% 4.87/1.90  tff(c_1118, plain, (~m1_subset_1('#skF_2'('#skF_8', '#skF_4', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_8', k2_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_676, c_1115])).
% 4.87/1.90  tff(c_1121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_811, c_972, c_1118])).
% 4.87/1.90  tff(c_1122, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 4.87/1.90  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.87/1.90  tff(c_1137, plain, (![B_317]: (r2_hidden(k4_tarski('#skF_7', '#skF_6'), B_317) | ~r1_tarski('#skF_5', B_317))), inference(resolution, [status(thm)], [c_1122, c_2])).
% 4.87/1.90  tff(c_16, plain, (![B_9, D_11, A_8, C_10]: (r2_hidden(B_9, D_11) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.87/1.90  tff(c_1152, plain, (![D_11, C_10]: (r2_hidden('#skF_6', D_11) | ~r1_tarski('#skF_5', k2_zfmisc_1(C_10, D_11)))), inference(resolution, [status(thm)], [c_1137, c_16])).
% 4.87/1.90  tff(c_1567, plain, (r2_hidden('#skF_6', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1558, c_1152])).
% 4.87/1.90  tff(c_1590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1193, c_1567])).
% 4.87/1.90  tff(c_1591, plain, (![E_80]: (~r2_hidden(k4_tarski(E_80, '#skF_8'), '#skF_5') | ~m1_subset_1(E_80, '#skF_4'))), inference(splitRight, [status(thm)], [c_1192])).
% 4.87/1.90  tff(c_1758, plain, (![B_404]: (~m1_subset_1('#skF_2'('#skF_8', B_404, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_8', k9_relat_1('#skF_5', B_404)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1754, c_1591])).
% 4.87/1.90  tff(c_2173, plain, (![B_450]: (~m1_subset_1('#skF_2'('#skF_8', B_450, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_8', k9_relat_1('#skF_5', B_450)))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1758])).
% 4.87/1.90  tff(c_2176, plain, (~m1_subset_1('#skF_2'('#skF_8', '#skF_4', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_8', k2_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_676, c_2173])).
% 4.87/1.90  tff(c_2178, plain, (~m1_subset_1('#skF_2'('#skF_8', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_811, c_2176])).
% 4.87/1.90  tff(c_1614, plain, (![A_381, B_382, C_383]: (r2_hidden('#skF_2'(A_381, B_382, C_383), B_382) | ~r2_hidden(A_381, k9_relat_1(C_383, B_382)) | ~v1_relat_1(C_383))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.87/1.90  tff(c_2179, plain, (![A_451, B_452, C_453]: (m1_subset_1('#skF_2'(A_451, B_452, C_453), B_452) | ~r2_hidden(A_451, k9_relat_1(C_453, B_452)) | ~v1_relat_1(C_453))), inference(resolution, [status(thm)], [c_1614, c_20])).
% 4.87/1.90  tff(c_2204, plain, (![A_451]: (m1_subset_1('#skF_2'(A_451, '#skF_4', '#skF_5'), '#skF_4') | ~r2_hidden(A_451, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_676, c_2179])).
% 4.87/1.90  tff(c_2220, plain, (![A_454]: (m1_subset_1('#skF_2'(A_454, '#skF_4', '#skF_5'), '#skF_4') | ~r2_hidden(A_454, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_2204])).
% 4.87/1.90  tff(c_2250, plain, (m1_subset_1('#skF_2'('#skF_8', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_811, c_2220])).
% 4.87/1.90  tff(c_2269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2178, c_2250])).
% 4.87/1.90  tff(c_2271, plain, (~r2_hidden('#skF_8', k2_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_64])).
% 4.87/1.90  tff(c_60, plain, (~r2_hidden('#skF_6', k2_relset_1('#skF_4', '#skF_3', '#skF_5')) | r2_hidden('#skF_8', k2_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.87/1.90  tff(c_2394, plain, (~r2_hidden('#skF_6', k2_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2271, c_60])).
% 4.87/1.90  tff(c_2595, plain, (~r2_hidden('#skF_6', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2593, c_2394])).
% 4.87/1.90  tff(c_3015, plain, (![D_586, C_587, B_588, A_589]: (m1_subset_1(D_586, k1_zfmisc_1(k2_zfmisc_1(C_587, B_588))) | ~r1_tarski(k2_relat_1(D_586), B_588) | ~m1_subset_1(D_586, k1_zfmisc_1(k2_zfmisc_1(C_587, A_589))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.87/1.90  tff(c_3035, plain, (![B_590]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_590))) | ~r1_tarski(k2_relat_1('#skF_5'), B_590))), inference(resolution, [status(thm)], [c_48, c_3015])).
% 4.87/1.90  tff(c_3067, plain, (![B_592]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_4', B_592)) | ~r1_tarski(k2_relat_1('#skF_5'), B_592))), inference(resolution, [status(thm)], [c_3035, c_22])).
% 4.87/1.90  tff(c_3072, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_4', k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_3067])).
% 4.87/1.90  tff(c_62, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5') | r2_hidden('#skF_8', k2_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.87/1.90  tff(c_2334, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2271, c_62])).
% 4.87/1.90  tff(c_2366, plain, (![C_482, B_483, A_484]: (r2_hidden(C_482, B_483) | ~r2_hidden(C_482, A_484) | ~r1_tarski(A_484, B_483))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.87/1.90  tff(c_2371, plain, (![B_483]: (r2_hidden(k4_tarski('#skF_7', '#skF_6'), B_483) | ~r1_tarski('#skF_5', B_483))), inference(resolution, [status(thm)], [c_2334, c_2366])).
% 4.87/1.90  tff(c_2518, plain, (![B_505, D_506, A_507, C_508]: (r2_hidden(B_505, D_506) | ~r2_hidden(k4_tarski(A_507, B_505), k2_zfmisc_1(C_508, D_506)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.87/1.90  tff(c_2523, plain, (![D_506, C_508]: (r2_hidden('#skF_6', D_506) | ~r1_tarski('#skF_5', k2_zfmisc_1(C_508, D_506)))), inference(resolution, [status(thm)], [c_2371, c_2518])).
% 4.87/1.90  tff(c_3084, plain, (r2_hidden('#skF_6', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3072, c_2523])).
% 4.87/1.90  tff(c_3108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2595, c_3084])).
% 4.87/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.90  
% 4.87/1.90  Inference rules
% 4.87/1.90  ----------------------
% 4.87/1.90  #Ref     : 0
% 4.87/1.90  #Sup     : 653
% 4.87/1.90  #Fact    : 0
% 4.87/1.90  #Define  : 0
% 4.87/1.90  #Split   : 19
% 4.87/1.90  #Chain   : 0
% 4.87/1.90  #Close   : 0
% 4.87/1.90  
% 4.87/1.90  Ordering : KBO
% 4.87/1.90  
% 4.87/1.90  Simplification rules
% 4.87/1.90  ----------------------
% 4.87/1.90  #Subsume      : 53
% 4.87/1.90  #Demod        : 125
% 4.87/1.90  #Tautology    : 126
% 4.87/1.90  #SimpNegUnit  : 5
% 4.87/1.90  #BackRed      : 9
% 4.87/1.90  
% 4.87/1.90  #Partial instantiations: 0
% 4.87/1.90  #Strategies tried      : 1
% 4.87/1.90  
% 4.87/1.90  Timing (in seconds)
% 4.87/1.90  ----------------------
% 4.87/1.91  Preprocessing        : 0.34
% 4.87/1.91  Parsing              : 0.17
% 4.87/1.91  CNF conversion       : 0.03
% 4.87/1.91  Main loop            : 0.79
% 4.87/1.91  Inferencing          : 0.29
% 4.87/1.91  Reduction            : 0.24
% 4.87/1.91  Demodulation         : 0.16
% 4.87/1.91  BG Simplification    : 0.03
% 4.87/1.91  Subsumption          : 0.15
% 4.87/1.91  Abstraction          : 0.04
% 4.87/1.91  MUC search           : 0.00
% 4.87/1.91  Cooper               : 0.00
% 4.87/1.91  Total                : 1.17
% 4.87/1.91  Index Insertion      : 0.00
% 4.87/1.91  Index Deletion       : 0.00
% 4.87/1.91  Index Matching       : 0.00
% 4.87/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
