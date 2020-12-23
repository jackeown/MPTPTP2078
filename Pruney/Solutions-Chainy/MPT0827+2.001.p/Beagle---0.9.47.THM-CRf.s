%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:14 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 284 expanded)
%              Number of leaves         :   42 ( 112 expanded)
%              Depth                    :   22
%              Number of atoms          :  190 ( 481 expanded)
%              Number of equality atoms :   33 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_122,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4634,plain,(
    ! [A_552,B_553,C_554] :
      ( k2_relset_1(A_552,B_553,C_554) = k2_relat_1(C_554)
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(A_552,B_553))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4652,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_4634])).

tff(c_794,plain,(
    ! [A_162,B_163,C_164] :
      ( k1_relset_1(A_162,B_163,C_164) = k1_relat_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_812,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_794])).

tff(c_60,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_77,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_813,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_77])).

tff(c_18,plain,(
    ! [A_7] : r1_tarski(k1_tarski(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_89,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(A_58,B_59)
      | ~ r1_tarski(k1_tarski(A_58),B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_103,plain,(
    ! [A_60] : r2_hidden(A_60,k1_zfmisc_1(A_60)) ),
    inference(resolution,[status(thm)],[c_18,c_89])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_107,plain,(
    ! [A_60] : m1_subset_1(A_60,k1_zfmisc_1(A_60)) ),
    inference(resolution,[status(thm)],[c_103,c_20])).

tff(c_234,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_249,plain,(
    ! [A_80,B_81] : v1_relat_1(k2_zfmisc_1(A_80,B_81)) ),
    inference(resolution,[status(thm)],[c_107,c_234])).

tff(c_156,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_172,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_156])).

tff(c_177,plain,(
    ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_177])).

tff(c_259,plain,(
    v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_62,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_58,plain,(
    ! [A_42] : m1_subset_1(k6_relat_1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_294,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_310,plain,(
    ! [A_42] : v1_relat_1(k6_relat_1(A_42)) ),
    inference(resolution,[status(thm)],[c_58,c_294])).

tff(c_552,plain,(
    ! [C_121,B_122,A_123] :
      ( v5_relat_1(C_121,B_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_568,plain,(
    ! [A_42] : v5_relat_1(k6_relat_1(A_42),A_42) ),
    inference(resolution,[status(thm)],[c_58,c_552])).

tff(c_34,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_374,plain,(
    ! [A_105,B_106] :
      ( k9_relat_1(k6_relat_1(A_105),B_106) = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_391,plain,(
    ! [A_107] : k9_relat_1(k6_relat_1(A_107),A_107) = A_107 ),
    inference(resolution,[status(thm)],[c_107,c_374])).

tff(c_36,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k9_relat_1(B_20,A_19),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_397,plain,(
    ! [A_107] :
      ( r1_tarski(A_107,k2_relat_1(k6_relat_1(A_107)))
      | ~ v1_relat_1(k6_relat_1(A_107)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_36])).

tff(c_405,plain,(
    ! [A_108] : r1_tarski(A_108,k2_relat_1(k6_relat_1(A_108))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_397])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_884,plain,(
    ! [A_176] :
      ( k2_relat_1(k6_relat_1(A_176)) = A_176
      | ~ r1_tarski(k2_relat_1(k6_relat_1(A_176)),A_176) ) ),
    inference(resolution,[status(thm)],[c_405,c_8])).

tff(c_896,plain,(
    ! [A_17] :
      ( k2_relat_1(k6_relat_1(A_17)) = A_17
      | ~ v5_relat_1(k6_relat_1(A_17),A_17)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_34,c_884])).

tff(c_903,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_568,c_896])).

tff(c_573,plain,(
    ! [C_127,A_128,B_129] :
      ( v4_relat_1(C_127,A_128)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_589,plain,(
    ! [A_42] : v4_relat_1(k6_relat_1(A_42),A_42) ),
    inference(resolution,[status(thm)],[c_58,c_573])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_689,plain,(
    ! [A_144,B_145] :
      ( k5_relat_1(k6_relat_1(A_144),B_145) = B_145
      | ~ r1_tarski(k1_relat_1(B_145),A_144)
      | ~ v1_relat_1(B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_708,plain,(
    ! [B_145] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_145)),B_145) = B_145
      | ~ v1_relat_1(B_145) ) ),
    inference(resolution,[status(thm)],[c_12,c_689])).

tff(c_924,plain,(
    ! [A_177] : k2_relat_1(k6_relat_1(A_177)) = A_177 ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_568,c_896])).

tff(c_44,plain,(
    ! [B_27,A_26] :
      ( k5_relat_1(B_27,k6_relat_1(A_26)) = B_27
      | ~ r1_tarski(k2_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_939,plain,(
    ! [A_177,A_26] :
      ( k5_relat_1(k6_relat_1(A_177),k6_relat_1(A_26)) = k6_relat_1(A_177)
      | ~ r1_tarski(A_177,A_26)
      | ~ v1_relat_1(k6_relat_1(A_177)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_44])).

tff(c_1686,plain,(
    ! [A_254,A_255] :
      ( k5_relat_1(k6_relat_1(A_254),k6_relat_1(A_255)) = k6_relat_1(A_254)
      | ~ r1_tarski(A_254,A_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_939])).

tff(c_1725,plain,(
    ! [A_255] :
      ( k6_relat_1(k1_relat_1(k6_relat_1(A_255))) = k6_relat_1(A_255)
      | ~ r1_tarski(k1_relat_1(k6_relat_1(A_255)),A_255)
      | ~ v1_relat_1(k6_relat_1(A_255)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_1686])).

tff(c_3557,plain,(
    ! [A_443] :
      ( k6_relat_1(k1_relat_1(k6_relat_1(A_443))) = k6_relat_1(A_443)
      | ~ r1_tarski(k1_relat_1(k6_relat_1(A_443)),A_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_1725])).

tff(c_3565,plain,(
    ! [A_15] :
      ( k6_relat_1(k1_relat_1(k6_relat_1(A_15))) = k6_relat_1(A_15)
      | ~ v4_relat_1(k6_relat_1(A_15),A_15)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_30,c_3557])).

tff(c_3573,plain,(
    ! [A_444] : k6_relat_1(k1_relat_1(k6_relat_1(A_444))) = k6_relat_1(A_444) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_589,c_3565])).

tff(c_3660,plain,(
    ! [A_444] : k2_relat_1(k6_relat_1(A_444)) = k1_relat_1(k6_relat_1(A_444)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3573,c_903])).

tff(c_3739,plain,(
    ! [A_445] : k1_relat_1(k6_relat_1(A_445)) = A_445 ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_3660])).

tff(c_40,plain,(
    ! [A_21,B_23] :
      ( r1_tarski(k1_relat_1(A_21),k1_relat_1(B_23))
      | ~ r1_tarski(A_21,B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3760,plain,(
    ! [A_445,B_23] :
      ( r1_tarski(A_445,k1_relat_1(B_23))
      | ~ r1_tarski(k6_relat_1(A_445),B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(k6_relat_1(A_445)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3739,c_40])).

tff(c_3992,plain,(
    ! [A_457,B_458] :
      ( r1_tarski(A_457,k1_relat_1(B_458))
      | ~ r1_tarski(k6_relat_1(A_457),B_458)
      | ~ v1_relat_1(B_458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_3760])).

tff(c_3998,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3992])).

tff(c_4008,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_3998])).

tff(c_4010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_813,c_4008])).

tff(c_4011,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_4653,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4652,c_4011])).

tff(c_4055,plain,(
    ! [C_469,A_470,B_471] :
      ( v1_relat_1(C_469)
      | ~ m1_subset_1(C_469,k1_zfmisc_1(k2_zfmisc_1(A_470,B_471))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4073,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_4055])).

tff(c_4072,plain,(
    ! [A_42] : v1_relat_1(k6_relat_1(A_42)) ),
    inference(resolution,[status(thm)],[c_58,c_4055])).

tff(c_4223,plain,(
    ! [C_496,B_497,A_498] :
      ( v5_relat_1(C_496,B_497)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(k2_zfmisc_1(A_498,B_497))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4240,plain,(
    ! [A_42] : v5_relat_1(k6_relat_1(A_42),A_42) ),
    inference(resolution,[status(thm)],[c_58,c_4223])).

tff(c_4018,plain,(
    ! [A_460,B_461] :
      ( r2_hidden(A_460,B_461)
      | ~ r1_tarski(k1_tarski(A_460),B_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4032,plain,(
    ! [A_462] : r2_hidden(A_462,k1_zfmisc_1(A_462)) ),
    inference(resolution,[status(thm)],[c_18,c_4018])).

tff(c_4036,plain,(
    ! [A_462] : m1_subset_1(A_462,k1_zfmisc_1(A_462)) ),
    inference(resolution,[status(thm)],[c_4032,c_20])).

tff(c_4326,plain,(
    ! [A_516,B_517] :
      ( k9_relat_1(k6_relat_1(A_516),B_517) = B_517
      | ~ m1_subset_1(B_517,k1_zfmisc_1(A_516)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4343,plain,(
    ! [A_518] : k9_relat_1(k6_relat_1(A_518),A_518) = A_518 ),
    inference(resolution,[status(thm)],[c_4036,c_4326])).

tff(c_4349,plain,(
    ! [A_518] :
      ( r1_tarski(A_518,k2_relat_1(k6_relat_1(A_518)))
      | ~ v1_relat_1(k6_relat_1(A_518)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4343,c_36])).

tff(c_4357,plain,(
    ! [A_519] : r1_tarski(A_519,k2_relat_1(k6_relat_1(A_519))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4072,c_4349])).

tff(c_4757,plain,(
    ! [A_570] :
      ( k2_relat_1(k6_relat_1(A_570)) = A_570
      | ~ r1_tarski(k2_relat_1(k6_relat_1(A_570)),A_570) ) ),
    inference(resolution,[status(thm)],[c_4357,c_8])).

tff(c_4769,plain,(
    ! [A_17] :
      ( k2_relat_1(k6_relat_1(A_17)) = A_17
      | ~ v5_relat_1(k6_relat_1(A_17),A_17)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_34,c_4757])).

tff(c_4797,plain,(
    ! [A_571] : k2_relat_1(k6_relat_1(A_571)) = A_571 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4072,c_4240,c_4769])).

tff(c_38,plain,(
    ! [A_21,B_23] :
      ( r1_tarski(k2_relat_1(A_21),k2_relat_1(B_23))
      | ~ r1_tarski(A_21,B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4803,plain,(
    ! [A_571,B_23] :
      ( r1_tarski(A_571,k2_relat_1(B_23))
      | ~ r1_tarski(k6_relat_1(A_571),B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(k6_relat_1(A_571)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4797,c_38])).

tff(c_5395,plain,(
    ! [A_637,B_638] :
      ( r1_tarski(A_637,k2_relat_1(B_638))
      | ~ r1_tarski(k6_relat_1(A_637),B_638)
      | ~ v1_relat_1(B_638) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4072,c_4803])).

tff(c_5401,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_5395])).

tff(c_5411,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4073,c_5401])).

tff(c_5413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4653,c_5411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:00:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.71/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.13  
% 5.75/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.13  %$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.75/2.13  
% 5.75/2.13  %Foreground sorts:
% 5.75/2.13  
% 5.75/2.13  
% 5.75/2.13  %Background operators:
% 5.75/2.13  
% 5.75/2.13  
% 5.75/2.13  %Foreground operators:
% 5.75/2.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.75/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.75/2.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.75/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.75/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.75/2.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.75/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.75/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.75/2.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.75/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.13  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.75/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.75/2.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.75/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.75/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.13  
% 5.75/2.15  tff(f_131, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 5.75/2.15  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.75/2.15  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.75/2.15  tff(f_44, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 5.75/2.15  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.75/2.15  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.75/2.15  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.75/2.15  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.75/2.15  tff(f_122, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.75/2.15  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.75/2.15  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.75/2.15  tff(f_102, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 5.75/2.15  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 5.75/2.15  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.75/2.15  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.75/2.15  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 5.75/2.15  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 5.75/2.15  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 5.75/2.15  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.75/2.15  tff(c_4634, plain, (![A_552, B_553, C_554]: (k2_relset_1(A_552, B_553, C_554)=k2_relat_1(C_554) | ~m1_subset_1(C_554, k1_zfmisc_1(k2_zfmisc_1(A_552, B_553))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.75/2.15  tff(c_4652, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_4634])).
% 5.75/2.15  tff(c_794, plain, (![A_162, B_163, C_164]: (k1_relset_1(A_162, B_163, C_164)=k1_relat_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.75/2.15  tff(c_812, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_794])).
% 5.75/2.15  tff(c_60, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.75/2.15  tff(c_77, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_60])).
% 5.75/2.15  tff(c_813, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_812, c_77])).
% 5.75/2.15  tff(c_18, plain, (![A_7]: (r1_tarski(k1_tarski(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.75/2.15  tff(c_89, plain, (![A_58, B_59]: (r2_hidden(A_58, B_59) | ~r1_tarski(k1_tarski(A_58), B_59))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.75/2.15  tff(c_103, plain, (![A_60]: (r2_hidden(A_60, k1_zfmisc_1(A_60)))), inference(resolution, [status(thm)], [c_18, c_89])).
% 5.75/2.15  tff(c_20, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.75/2.15  tff(c_107, plain, (![A_60]: (m1_subset_1(A_60, k1_zfmisc_1(A_60)))), inference(resolution, [status(thm)], [c_103, c_20])).
% 5.75/2.15  tff(c_234, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.75/2.15  tff(c_249, plain, (![A_80, B_81]: (v1_relat_1(k2_zfmisc_1(A_80, B_81)))), inference(resolution, [status(thm)], [c_107, c_234])).
% 5.75/2.15  tff(c_156, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.75/2.15  tff(c_172, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_156])).
% 5.75/2.15  tff(c_177, plain, (~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_172])).
% 5.75/2.15  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_177])).
% 5.75/2.15  tff(c_259, plain, (v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_172])).
% 5.75/2.15  tff(c_62, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.75/2.15  tff(c_58, plain, (![A_42]: (m1_subset_1(k6_relat_1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.75/2.15  tff(c_294, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.75/2.15  tff(c_310, plain, (![A_42]: (v1_relat_1(k6_relat_1(A_42)))), inference(resolution, [status(thm)], [c_58, c_294])).
% 5.75/2.15  tff(c_552, plain, (![C_121, B_122, A_123]: (v5_relat_1(C_121, B_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.75/2.15  tff(c_568, plain, (![A_42]: (v5_relat_1(k6_relat_1(A_42), A_42))), inference(resolution, [status(thm)], [c_58, c_552])).
% 5.75/2.15  tff(c_34, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.75/2.15  tff(c_374, plain, (![A_105, B_106]: (k9_relat_1(k6_relat_1(A_105), B_106)=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.75/2.15  tff(c_391, plain, (![A_107]: (k9_relat_1(k6_relat_1(A_107), A_107)=A_107)), inference(resolution, [status(thm)], [c_107, c_374])).
% 5.75/2.15  tff(c_36, plain, (![B_20, A_19]: (r1_tarski(k9_relat_1(B_20, A_19), k2_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.75/2.15  tff(c_397, plain, (![A_107]: (r1_tarski(A_107, k2_relat_1(k6_relat_1(A_107))) | ~v1_relat_1(k6_relat_1(A_107)))), inference(superposition, [status(thm), theory('equality')], [c_391, c_36])).
% 5.75/2.15  tff(c_405, plain, (![A_108]: (r1_tarski(A_108, k2_relat_1(k6_relat_1(A_108))))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_397])).
% 5.75/2.15  tff(c_8, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.15  tff(c_884, plain, (![A_176]: (k2_relat_1(k6_relat_1(A_176))=A_176 | ~r1_tarski(k2_relat_1(k6_relat_1(A_176)), A_176))), inference(resolution, [status(thm)], [c_405, c_8])).
% 5.75/2.15  tff(c_896, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17 | ~v5_relat_1(k6_relat_1(A_17), A_17) | ~v1_relat_1(k6_relat_1(A_17)))), inference(resolution, [status(thm)], [c_34, c_884])).
% 5.75/2.15  tff(c_903, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_310, c_568, c_896])).
% 5.75/2.15  tff(c_573, plain, (![C_127, A_128, B_129]: (v4_relat_1(C_127, A_128) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.75/2.15  tff(c_589, plain, (![A_42]: (v4_relat_1(k6_relat_1(A_42), A_42))), inference(resolution, [status(thm)], [c_58, c_573])).
% 5.75/2.15  tff(c_30, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.75/2.15  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.15  tff(c_689, plain, (![A_144, B_145]: (k5_relat_1(k6_relat_1(A_144), B_145)=B_145 | ~r1_tarski(k1_relat_1(B_145), A_144) | ~v1_relat_1(B_145))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.75/2.15  tff(c_708, plain, (![B_145]: (k5_relat_1(k6_relat_1(k1_relat_1(B_145)), B_145)=B_145 | ~v1_relat_1(B_145))), inference(resolution, [status(thm)], [c_12, c_689])).
% 5.75/2.15  tff(c_924, plain, (![A_177]: (k2_relat_1(k6_relat_1(A_177))=A_177)), inference(demodulation, [status(thm), theory('equality')], [c_310, c_568, c_896])).
% 5.75/2.15  tff(c_44, plain, (![B_27, A_26]: (k5_relat_1(B_27, k6_relat_1(A_26))=B_27 | ~r1_tarski(k2_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.75/2.15  tff(c_939, plain, (![A_177, A_26]: (k5_relat_1(k6_relat_1(A_177), k6_relat_1(A_26))=k6_relat_1(A_177) | ~r1_tarski(A_177, A_26) | ~v1_relat_1(k6_relat_1(A_177)))), inference(superposition, [status(thm), theory('equality')], [c_924, c_44])).
% 5.75/2.15  tff(c_1686, plain, (![A_254, A_255]: (k5_relat_1(k6_relat_1(A_254), k6_relat_1(A_255))=k6_relat_1(A_254) | ~r1_tarski(A_254, A_255))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_939])).
% 5.75/2.15  tff(c_1725, plain, (![A_255]: (k6_relat_1(k1_relat_1(k6_relat_1(A_255)))=k6_relat_1(A_255) | ~r1_tarski(k1_relat_1(k6_relat_1(A_255)), A_255) | ~v1_relat_1(k6_relat_1(A_255)))), inference(superposition, [status(thm), theory('equality')], [c_708, c_1686])).
% 5.75/2.15  tff(c_3557, plain, (![A_443]: (k6_relat_1(k1_relat_1(k6_relat_1(A_443)))=k6_relat_1(A_443) | ~r1_tarski(k1_relat_1(k6_relat_1(A_443)), A_443))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_1725])).
% 5.75/2.15  tff(c_3565, plain, (![A_15]: (k6_relat_1(k1_relat_1(k6_relat_1(A_15)))=k6_relat_1(A_15) | ~v4_relat_1(k6_relat_1(A_15), A_15) | ~v1_relat_1(k6_relat_1(A_15)))), inference(resolution, [status(thm)], [c_30, c_3557])).
% 5.75/2.15  tff(c_3573, plain, (![A_444]: (k6_relat_1(k1_relat_1(k6_relat_1(A_444)))=k6_relat_1(A_444))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_589, c_3565])).
% 5.75/2.15  tff(c_3660, plain, (![A_444]: (k2_relat_1(k6_relat_1(A_444))=k1_relat_1(k6_relat_1(A_444)))), inference(superposition, [status(thm), theory('equality')], [c_3573, c_903])).
% 5.75/2.15  tff(c_3739, plain, (![A_445]: (k1_relat_1(k6_relat_1(A_445))=A_445)), inference(demodulation, [status(thm), theory('equality')], [c_903, c_3660])).
% 5.75/2.15  tff(c_40, plain, (![A_21, B_23]: (r1_tarski(k1_relat_1(A_21), k1_relat_1(B_23)) | ~r1_tarski(A_21, B_23) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.75/2.15  tff(c_3760, plain, (![A_445, B_23]: (r1_tarski(A_445, k1_relat_1(B_23)) | ~r1_tarski(k6_relat_1(A_445), B_23) | ~v1_relat_1(B_23) | ~v1_relat_1(k6_relat_1(A_445)))), inference(superposition, [status(thm), theory('equality')], [c_3739, c_40])).
% 5.75/2.15  tff(c_3992, plain, (![A_457, B_458]: (r1_tarski(A_457, k1_relat_1(B_458)) | ~r1_tarski(k6_relat_1(A_457), B_458) | ~v1_relat_1(B_458))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_3760])).
% 5.75/2.15  tff(c_3998, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3992])).
% 5.75/2.15  tff(c_4008, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_3998])).
% 5.75/2.15  tff(c_4010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_813, c_4008])).
% 5.75/2.15  tff(c_4011, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_60])).
% 5.75/2.15  tff(c_4653, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4652, c_4011])).
% 5.75/2.15  tff(c_4055, plain, (![C_469, A_470, B_471]: (v1_relat_1(C_469) | ~m1_subset_1(C_469, k1_zfmisc_1(k2_zfmisc_1(A_470, B_471))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.75/2.15  tff(c_4073, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_4055])).
% 5.75/2.15  tff(c_4072, plain, (![A_42]: (v1_relat_1(k6_relat_1(A_42)))), inference(resolution, [status(thm)], [c_58, c_4055])).
% 5.75/2.15  tff(c_4223, plain, (![C_496, B_497, A_498]: (v5_relat_1(C_496, B_497) | ~m1_subset_1(C_496, k1_zfmisc_1(k2_zfmisc_1(A_498, B_497))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.75/2.15  tff(c_4240, plain, (![A_42]: (v5_relat_1(k6_relat_1(A_42), A_42))), inference(resolution, [status(thm)], [c_58, c_4223])).
% 5.75/2.15  tff(c_4018, plain, (![A_460, B_461]: (r2_hidden(A_460, B_461) | ~r1_tarski(k1_tarski(A_460), B_461))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.75/2.15  tff(c_4032, plain, (![A_462]: (r2_hidden(A_462, k1_zfmisc_1(A_462)))), inference(resolution, [status(thm)], [c_18, c_4018])).
% 5.75/2.15  tff(c_4036, plain, (![A_462]: (m1_subset_1(A_462, k1_zfmisc_1(A_462)))), inference(resolution, [status(thm)], [c_4032, c_20])).
% 5.75/2.15  tff(c_4326, plain, (![A_516, B_517]: (k9_relat_1(k6_relat_1(A_516), B_517)=B_517 | ~m1_subset_1(B_517, k1_zfmisc_1(A_516)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.75/2.15  tff(c_4343, plain, (![A_518]: (k9_relat_1(k6_relat_1(A_518), A_518)=A_518)), inference(resolution, [status(thm)], [c_4036, c_4326])).
% 5.75/2.15  tff(c_4349, plain, (![A_518]: (r1_tarski(A_518, k2_relat_1(k6_relat_1(A_518))) | ~v1_relat_1(k6_relat_1(A_518)))), inference(superposition, [status(thm), theory('equality')], [c_4343, c_36])).
% 5.75/2.15  tff(c_4357, plain, (![A_519]: (r1_tarski(A_519, k2_relat_1(k6_relat_1(A_519))))), inference(demodulation, [status(thm), theory('equality')], [c_4072, c_4349])).
% 5.75/2.15  tff(c_4757, plain, (![A_570]: (k2_relat_1(k6_relat_1(A_570))=A_570 | ~r1_tarski(k2_relat_1(k6_relat_1(A_570)), A_570))), inference(resolution, [status(thm)], [c_4357, c_8])).
% 5.75/2.15  tff(c_4769, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17 | ~v5_relat_1(k6_relat_1(A_17), A_17) | ~v1_relat_1(k6_relat_1(A_17)))), inference(resolution, [status(thm)], [c_34, c_4757])).
% 5.75/2.15  tff(c_4797, plain, (![A_571]: (k2_relat_1(k6_relat_1(A_571))=A_571)), inference(demodulation, [status(thm), theory('equality')], [c_4072, c_4240, c_4769])).
% 5.75/2.15  tff(c_38, plain, (![A_21, B_23]: (r1_tarski(k2_relat_1(A_21), k2_relat_1(B_23)) | ~r1_tarski(A_21, B_23) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.75/2.15  tff(c_4803, plain, (![A_571, B_23]: (r1_tarski(A_571, k2_relat_1(B_23)) | ~r1_tarski(k6_relat_1(A_571), B_23) | ~v1_relat_1(B_23) | ~v1_relat_1(k6_relat_1(A_571)))), inference(superposition, [status(thm), theory('equality')], [c_4797, c_38])).
% 5.75/2.15  tff(c_5395, plain, (![A_637, B_638]: (r1_tarski(A_637, k2_relat_1(B_638)) | ~r1_tarski(k6_relat_1(A_637), B_638) | ~v1_relat_1(B_638))), inference(demodulation, [status(thm), theory('equality')], [c_4072, c_4803])).
% 5.75/2.15  tff(c_5401, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_5395])).
% 5.75/2.15  tff(c_5411, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4073, c_5401])).
% 5.75/2.15  tff(c_5413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4653, c_5411])).
% 5.75/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.15  
% 5.75/2.15  Inference rules
% 5.75/2.15  ----------------------
% 5.75/2.15  #Ref     : 0
% 5.75/2.15  #Sup     : 1010
% 5.75/2.15  #Fact    : 0
% 5.75/2.15  #Define  : 0
% 5.75/2.15  #Split   : 16
% 5.75/2.15  #Chain   : 0
% 5.75/2.15  #Close   : 0
% 5.75/2.15  
% 5.75/2.15  Ordering : KBO
% 5.75/2.15  
% 5.75/2.15  Simplification rules
% 5.75/2.15  ----------------------
% 5.75/2.15  #Subsume      : 112
% 5.75/2.15  #Demod        : 761
% 5.75/2.15  #Tautology    : 386
% 5.75/2.15  #SimpNegUnit  : 6
% 5.75/2.15  #BackRed      : 45
% 5.75/2.15  
% 5.75/2.15  #Partial instantiations: 0
% 5.75/2.15  #Strategies tried      : 1
% 5.75/2.15  
% 5.75/2.15  Timing (in seconds)
% 5.75/2.15  ----------------------
% 5.75/2.15  Preprocessing        : 0.35
% 5.75/2.15  Parsing              : 0.19
% 5.75/2.15  CNF conversion       : 0.02
% 5.75/2.15  Main loop            : 1.03
% 5.75/2.16  Inferencing          : 0.36
% 5.75/2.16  Reduction            : 0.37
% 5.75/2.16  Demodulation         : 0.27
% 5.75/2.16  BG Simplification    : 0.04
% 5.75/2.16  Subsumption          : 0.18
% 5.75/2.16  Abstraction          : 0.05
% 5.75/2.16  MUC search           : 0.00
% 5.75/2.16  Cooper               : 0.00
% 5.75/2.16  Total                : 1.42
% 5.75/2.16  Index Insertion      : 0.00
% 5.75/2.16  Index Deletion       : 0.00
% 5.75/2.16  Index Matching       : 0.00
% 5.75/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
