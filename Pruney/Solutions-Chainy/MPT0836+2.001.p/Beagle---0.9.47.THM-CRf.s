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
% DateTime   : Thu Dec  3 10:08:02 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 194 expanded)
%              Number of leaves         :   41 (  85 expanded)
%              Depth                    :    9
%              Number of atoms          :  178 ( 463 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_60,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_88,plain,(
    ! [C_95,A_96,B_97] :
      ( v1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_92,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_88])).

tff(c_3730,plain,(
    ! [A_415,B_416,C_417] :
      ( k1_relset_1(A_415,B_416,C_417) = k1_relat_1(C_417)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3734,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_3730])).

tff(c_334,plain,(
    ! [A_155,B_156,C_157] :
      ( k1_relset_1(A_155,B_156,C_157) = k1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_338,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_334])).

tff(c_76,plain,
    ( r2_hidden('#skF_11',k1_relset_1('#skF_8','#skF_9','#skF_10'))
    | m1_subset_1('#skF_12','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_93,plain,(
    m1_subset_1('#skF_12','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,
    ( r2_hidden('#skF_11',k1_relset_1('#skF_8','#skF_9','#skF_10'))
    | r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_117,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_30,plain,(
    ! [C_28,A_13,D_31] :
      ( r2_hidden(C_28,k1_relat_1(A_13))
      | ~ r2_hidden(k4_tarski(C_28,D_31),A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_124,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_117,c_30])).

tff(c_172,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_176,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_172])).

tff(c_66,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_89),'#skF_10')
      | ~ m1_subset_1(E_89,'#skF_9')
      | ~ r2_hidden('#skF_11',k1_relset_1('#skF_8','#skF_9','#skF_10')) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_272,plain,(
    ! [E_146] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_146),'#skF_10')
      | ~ m1_subset_1(E_146,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_176,c_66])).

tff(c_279,plain,(
    ~ m1_subset_1('#skF_12','#skF_9') ),
    inference(resolution,[status(thm)],[c_117,c_272])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_279])).

tff(c_287,plain,(
    r2_hidden('#skF_11',k1_relset_1('#skF_8','#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_342,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_287])).

tff(c_112,plain,(
    ! [C_114,B_115,A_116] :
      ( v5_relat_1(C_114,B_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_116,plain,(
    v5_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_112])).

tff(c_48,plain,(
    ! [A_38] :
      ( k10_relat_1(A_38,k2_relat_1(A_38)) = k1_relat_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_442,plain,(
    ! [A_174,B_175,C_176] :
      ( r2_hidden('#skF_7'(A_174,B_175,C_176),k2_relat_1(C_176))
      | ~ r2_hidden(A_174,k10_relat_1(C_176,B_175))
      | ~ v1_relat_1(C_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_98,plain,(
    ! [B_109,A_110] :
      ( r1_tarski(k2_relat_1(B_109),A_110)
      | ~ v5_relat_1(B_109,A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_312,plain,(
    ! [B_150,A_151] :
      ( k3_xboole_0(k2_relat_1(B_150),A_151) = k2_relat_1(B_150)
      | ~ v5_relat_1(B_150,A_151)
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_98,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_324,plain,(
    ! [D_6,A_151,B_150] :
      ( r2_hidden(D_6,A_151)
      | ~ r2_hidden(D_6,k2_relat_1(B_150))
      | ~ v5_relat_1(B_150,A_151)
      | ~ v1_relat_1(B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_4])).

tff(c_1566,plain,(
    ! [A_270,B_271,C_272,A_273] :
      ( r2_hidden('#skF_7'(A_270,B_271,C_272),A_273)
      | ~ v5_relat_1(C_272,A_273)
      | ~ r2_hidden(A_270,k10_relat_1(C_272,B_271))
      | ~ v1_relat_1(C_272) ) ),
    inference(resolution,[status(thm)],[c_442,c_324])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1598,plain,(
    ! [A_274,B_275,C_276,A_277] :
      ( m1_subset_1('#skF_7'(A_274,B_275,C_276),A_277)
      | ~ v5_relat_1(C_276,A_277)
      | ~ r2_hidden(A_274,k10_relat_1(C_276,B_275))
      | ~ v1_relat_1(C_276) ) ),
    inference(resolution,[status(thm)],[c_1566,c_22])).

tff(c_3634,plain,(
    ! [A_384,A_385,A_386] :
      ( m1_subset_1('#skF_7'(A_384,k2_relat_1(A_385),A_385),A_386)
      | ~ v5_relat_1(A_385,A_386)
      | ~ r2_hidden(A_384,k1_relat_1(A_385))
      | ~ v1_relat_1(A_385)
      | ~ v1_relat_1(A_385) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1598])).

tff(c_456,plain,(
    ! [A_183,B_184,C_185] :
      ( r2_hidden(k4_tarski(A_183,'#skF_7'(A_183,B_184,C_185)),C_185)
      | ~ r2_hidden(A_183,k10_relat_1(C_185,B_184))
      | ~ v1_relat_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_288,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_70,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_89),'#skF_10')
      | ~ m1_subset_1(E_89,'#skF_9')
      | r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_339,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_89),'#skF_10')
      | ~ m1_subset_1(E_89,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_70])).

tff(c_466,plain,(
    ! [B_184] :
      ( ~ m1_subset_1('#skF_7'('#skF_11',B_184,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_184))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_456,c_339])).

tff(c_564,plain,(
    ! [B_192] :
      ( ~ m1_subset_1('#skF_7'('#skF_11',B_192,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_192)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_466])).

tff(c_568,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_11',k2_relat_1('#skF_10'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_564])).

tff(c_570,plain,(
    ~ m1_subset_1('#skF_7'('#skF_11',k2_relat_1('#skF_10'),'#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_342,c_568])).

tff(c_3637,plain,
    ( ~ v5_relat_1('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_3634,c_570])).

tff(c_3657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_342,c_116,c_3637])).

tff(c_3658,plain,(
    r2_hidden('#skF_11',k1_relset_1('#skF_8','#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3736,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3734,c_3658])).

tff(c_3667,plain,(
    ! [C_393,B_394,A_395] :
      ( v5_relat_1(C_393,B_394)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_395,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3671,plain,(
    v5_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_3667])).

tff(c_3836,plain,(
    ! [A_433,B_434,C_435] :
      ( r2_hidden('#skF_7'(A_433,B_434,C_435),k2_relat_1(C_435))
      | ~ r2_hidden(A_433,k10_relat_1(C_435,B_434))
      | ~ v1_relat_1(C_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3679,plain,(
    ! [B_404,A_405] :
      ( r1_tarski(k2_relat_1(B_404),A_405)
      | ~ v5_relat_1(B_404,A_405)
      | ~ v1_relat_1(B_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3708,plain,(
    ! [B_410,A_411] :
      ( k3_xboole_0(k2_relat_1(B_410),A_411) = k2_relat_1(B_410)
      | ~ v5_relat_1(B_410,A_411)
      | ~ v1_relat_1(B_410) ) ),
    inference(resolution,[status(thm)],[c_3679,c_20])).

tff(c_3717,plain,(
    ! [D_6,A_411,B_410] :
      ( r2_hidden(D_6,A_411)
      | ~ r2_hidden(D_6,k2_relat_1(B_410))
      | ~ v5_relat_1(B_410,A_411)
      | ~ v1_relat_1(B_410) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3708,c_4])).

tff(c_4962,plain,(
    ! [A_529,B_530,C_531,A_532] :
      ( r2_hidden('#skF_7'(A_529,B_530,C_531),A_532)
      | ~ v5_relat_1(C_531,A_532)
      | ~ r2_hidden(A_529,k10_relat_1(C_531,B_530))
      | ~ v1_relat_1(C_531) ) ),
    inference(resolution,[status(thm)],[c_3836,c_3717])).

tff(c_5097,plain,(
    ! [A_540,B_541,C_542,A_543] :
      ( m1_subset_1('#skF_7'(A_540,B_541,C_542),A_543)
      | ~ v5_relat_1(C_542,A_543)
      | ~ r2_hidden(A_540,k10_relat_1(C_542,B_541))
      | ~ v1_relat_1(C_542) ) ),
    inference(resolution,[status(thm)],[c_4962,c_22])).

tff(c_7023,plain,(
    ! [A_644,A_645,A_646] :
      ( m1_subset_1('#skF_7'(A_644,k2_relat_1(A_645),A_645),A_646)
      | ~ v5_relat_1(A_645,A_646)
      | ~ r2_hidden(A_644,k1_relat_1(A_645))
      | ~ v1_relat_1(A_645)
      | ~ v1_relat_1(A_645) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_5097])).

tff(c_3850,plain,(
    ! [A_442,B_443,C_444] :
      ( r2_hidden(k4_tarski(A_442,'#skF_7'(A_442,B_443,C_444)),C_444)
      | ~ r2_hidden(A_442,k10_relat_1(C_444,B_443))
      | ~ v1_relat_1(C_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3659,plain,(
    ~ m1_subset_1('#skF_12','#skF_9') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_74,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_89),'#skF_10')
      | ~ m1_subset_1(E_89,'#skF_9')
      | m1_subset_1('#skF_12','#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3706,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_89),'#skF_10')
      | ~ m1_subset_1(E_89,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3659,c_74])).

tff(c_3860,plain,(
    ! [B_443] :
      ( ~ m1_subset_1('#skF_7'('#skF_11',B_443,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_443))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_3850,c_3706])).

tff(c_3884,plain,(
    ! [B_445] :
      ( ~ m1_subset_1('#skF_7'('#skF_11',B_445,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_445)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_3860])).

tff(c_3888,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_11',k2_relat_1('#skF_10'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_3884])).

tff(c_3890,plain,(
    ~ m1_subset_1('#skF_7'('#skF_11',k2_relat_1('#skF_10'),'#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_3736,c_3888])).

tff(c_7026,plain,
    ( ~ v5_relat_1('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_7023,c_3890])).

tff(c_7046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_3736,c_3671,c_7026])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.02/2.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.02/2.45  
% 7.02/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.19/2.45  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_12 > #skF_4
% 7.19/2.45  
% 7.19/2.45  %Foreground sorts:
% 7.19/2.45  
% 7.19/2.45  
% 7.19/2.45  %Background operators:
% 7.19/2.45  
% 7.19/2.45  
% 7.19/2.45  %Foreground operators:
% 7.19/2.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.19/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.19/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.19/2.45  tff('#skF_11', type, '#skF_11': $i).
% 7.19/2.45  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.19/2.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.19/2.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.19/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.19/2.45  tff('#skF_10', type, '#skF_10': $i).
% 7.19/2.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.19/2.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.19/2.45  tff('#skF_9', type, '#skF_9': $i).
% 7.19/2.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.19/2.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.19/2.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.19/2.45  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.19/2.45  tff('#skF_8', type, '#skF_8': $i).
% 7.19/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.19/2.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.19/2.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.19/2.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.19/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.19/2.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.19/2.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.19/2.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.19/2.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.19/2.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.19/2.45  tff('#skF_12', type, '#skF_12': $i).
% 7.19/2.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.19/2.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.19/2.45  
% 7.19/2.47  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relset_1)).
% 7.19/2.47  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.19/2.47  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.19/2.47  tff(f_56, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 7.19/2.47  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.19/2.47  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 7.19/2.47  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 7.19/2.47  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.19/2.47  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.19/2.47  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.19/2.47  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 7.19/2.47  tff(c_60, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.19/2.47  tff(c_88, plain, (![C_95, A_96, B_97]: (v1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.19/2.47  tff(c_92, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_88])).
% 7.19/2.47  tff(c_3730, plain, (![A_415, B_416, C_417]: (k1_relset_1(A_415, B_416, C_417)=k1_relat_1(C_417) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.19/2.47  tff(c_3734, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_3730])).
% 7.19/2.47  tff(c_334, plain, (![A_155, B_156, C_157]: (k1_relset_1(A_155, B_156, C_157)=k1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.19/2.47  tff(c_338, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_334])).
% 7.19/2.47  tff(c_76, plain, (r2_hidden('#skF_11', k1_relset_1('#skF_8', '#skF_9', '#skF_10')) | m1_subset_1('#skF_12', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.19/2.47  tff(c_93, plain, (m1_subset_1('#skF_12', '#skF_9')), inference(splitLeft, [status(thm)], [c_76])).
% 7.19/2.47  tff(c_72, plain, (r2_hidden('#skF_11', k1_relset_1('#skF_8', '#skF_9', '#skF_10')) | r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.19/2.47  tff(c_117, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10')), inference(splitLeft, [status(thm)], [c_72])).
% 7.19/2.47  tff(c_30, plain, (![C_28, A_13, D_31]: (r2_hidden(C_28, k1_relat_1(A_13)) | ~r2_hidden(k4_tarski(C_28, D_31), A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.19/2.47  tff(c_124, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_117, c_30])).
% 7.19/2.47  tff(c_172, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.19/2.47  tff(c_176, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_172])).
% 7.19/2.47  tff(c_66, plain, (![E_89]: (~r2_hidden(k4_tarski('#skF_11', E_89), '#skF_10') | ~m1_subset_1(E_89, '#skF_9') | ~r2_hidden('#skF_11', k1_relset_1('#skF_8', '#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.19/2.47  tff(c_272, plain, (![E_146]: (~r2_hidden(k4_tarski('#skF_11', E_146), '#skF_10') | ~m1_subset_1(E_146, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_176, c_66])).
% 7.19/2.47  tff(c_279, plain, (~m1_subset_1('#skF_12', '#skF_9')), inference(resolution, [status(thm)], [c_117, c_272])).
% 7.19/2.47  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_279])).
% 7.19/2.47  tff(c_287, plain, (r2_hidden('#skF_11', k1_relset_1('#skF_8', '#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_72])).
% 7.19/2.47  tff(c_342, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_287])).
% 7.19/2.47  tff(c_112, plain, (![C_114, B_115, A_116]: (v5_relat_1(C_114, B_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.19/2.47  tff(c_116, plain, (v5_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_60, c_112])).
% 7.19/2.47  tff(c_48, plain, (![A_38]: (k10_relat_1(A_38, k2_relat_1(A_38))=k1_relat_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.19/2.47  tff(c_442, plain, (![A_174, B_175, C_176]: (r2_hidden('#skF_7'(A_174, B_175, C_176), k2_relat_1(C_176)) | ~r2_hidden(A_174, k10_relat_1(C_176, B_175)) | ~v1_relat_1(C_176))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.19/2.47  tff(c_98, plain, (![B_109, A_110]: (r1_tarski(k2_relat_1(B_109), A_110) | ~v5_relat_1(B_109, A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.19/2.47  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.19/2.47  tff(c_312, plain, (![B_150, A_151]: (k3_xboole_0(k2_relat_1(B_150), A_151)=k2_relat_1(B_150) | ~v5_relat_1(B_150, A_151) | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_98, c_20])).
% 7.19/2.47  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.19/2.47  tff(c_324, plain, (![D_6, A_151, B_150]: (r2_hidden(D_6, A_151) | ~r2_hidden(D_6, k2_relat_1(B_150)) | ~v5_relat_1(B_150, A_151) | ~v1_relat_1(B_150))), inference(superposition, [status(thm), theory('equality')], [c_312, c_4])).
% 7.19/2.47  tff(c_1566, plain, (![A_270, B_271, C_272, A_273]: (r2_hidden('#skF_7'(A_270, B_271, C_272), A_273) | ~v5_relat_1(C_272, A_273) | ~r2_hidden(A_270, k10_relat_1(C_272, B_271)) | ~v1_relat_1(C_272))), inference(resolution, [status(thm)], [c_442, c_324])).
% 7.19/2.47  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.19/2.47  tff(c_1598, plain, (![A_274, B_275, C_276, A_277]: (m1_subset_1('#skF_7'(A_274, B_275, C_276), A_277) | ~v5_relat_1(C_276, A_277) | ~r2_hidden(A_274, k10_relat_1(C_276, B_275)) | ~v1_relat_1(C_276))), inference(resolution, [status(thm)], [c_1566, c_22])).
% 7.19/2.47  tff(c_3634, plain, (![A_384, A_385, A_386]: (m1_subset_1('#skF_7'(A_384, k2_relat_1(A_385), A_385), A_386) | ~v5_relat_1(A_385, A_386) | ~r2_hidden(A_384, k1_relat_1(A_385)) | ~v1_relat_1(A_385) | ~v1_relat_1(A_385))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1598])).
% 7.19/2.47  tff(c_456, plain, (![A_183, B_184, C_185]: (r2_hidden(k4_tarski(A_183, '#skF_7'(A_183, B_184, C_185)), C_185) | ~r2_hidden(A_183, k10_relat_1(C_185, B_184)) | ~v1_relat_1(C_185))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.19/2.47  tff(c_288, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10')), inference(splitRight, [status(thm)], [c_72])).
% 7.19/2.47  tff(c_70, plain, (![E_89]: (~r2_hidden(k4_tarski('#skF_11', E_89), '#skF_10') | ~m1_subset_1(E_89, '#skF_9') | r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.19/2.47  tff(c_339, plain, (![E_89]: (~r2_hidden(k4_tarski('#skF_11', E_89), '#skF_10') | ~m1_subset_1(E_89, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_288, c_70])).
% 7.19/2.47  tff(c_466, plain, (![B_184]: (~m1_subset_1('#skF_7'('#skF_11', B_184, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_184)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_456, c_339])).
% 7.19/2.47  tff(c_564, plain, (![B_192]: (~m1_subset_1('#skF_7'('#skF_11', B_192, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_192)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_466])).
% 7.19/2.47  tff(c_568, plain, (~m1_subset_1('#skF_7'('#skF_11', k2_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_48, c_564])).
% 7.19/2.47  tff(c_570, plain, (~m1_subset_1('#skF_7'('#skF_11', k2_relat_1('#skF_10'), '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_342, c_568])).
% 7.19/2.47  tff(c_3637, plain, (~v5_relat_1('#skF_10', '#skF_9') | ~r2_hidden('#skF_11', k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_3634, c_570])).
% 7.19/2.47  tff(c_3657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_342, c_116, c_3637])).
% 7.19/2.47  tff(c_3658, plain, (r2_hidden('#skF_11', k1_relset_1('#skF_8', '#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_76])).
% 7.19/2.47  tff(c_3736, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_3734, c_3658])).
% 7.19/2.47  tff(c_3667, plain, (![C_393, B_394, A_395]: (v5_relat_1(C_393, B_394) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_395, B_394))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.19/2.47  tff(c_3671, plain, (v5_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_60, c_3667])).
% 7.19/2.47  tff(c_3836, plain, (![A_433, B_434, C_435]: (r2_hidden('#skF_7'(A_433, B_434, C_435), k2_relat_1(C_435)) | ~r2_hidden(A_433, k10_relat_1(C_435, B_434)) | ~v1_relat_1(C_435))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.19/2.47  tff(c_3679, plain, (![B_404, A_405]: (r1_tarski(k2_relat_1(B_404), A_405) | ~v5_relat_1(B_404, A_405) | ~v1_relat_1(B_404))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.19/2.47  tff(c_3708, plain, (![B_410, A_411]: (k3_xboole_0(k2_relat_1(B_410), A_411)=k2_relat_1(B_410) | ~v5_relat_1(B_410, A_411) | ~v1_relat_1(B_410))), inference(resolution, [status(thm)], [c_3679, c_20])).
% 7.19/2.47  tff(c_3717, plain, (![D_6, A_411, B_410]: (r2_hidden(D_6, A_411) | ~r2_hidden(D_6, k2_relat_1(B_410)) | ~v5_relat_1(B_410, A_411) | ~v1_relat_1(B_410))), inference(superposition, [status(thm), theory('equality')], [c_3708, c_4])).
% 7.19/2.47  tff(c_4962, plain, (![A_529, B_530, C_531, A_532]: (r2_hidden('#skF_7'(A_529, B_530, C_531), A_532) | ~v5_relat_1(C_531, A_532) | ~r2_hidden(A_529, k10_relat_1(C_531, B_530)) | ~v1_relat_1(C_531))), inference(resolution, [status(thm)], [c_3836, c_3717])).
% 7.19/2.47  tff(c_5097, plain, (![A_540, B_541, C_542, A_543]: (m1_subset_1('#skF_7'(A_540, B_541, C_542), A_543) | ~v5_relat_1(C_542, A_543) | ~r2_hidden(A_540, k10_relat_1(C_542, B_541)) | ~v1_relat_1(C_542))), inference(resolution, [status(thm)], [c_4962, c_22])).
% 7.19/2.47  tff(c_7023, plain, (![A_644, A_645, A_646]: (m1_subset_1('#skF_7'(A_644, k2_relat_1(A_645), A_645), A_646) | ~v5_relat_1(A_645, A_646) | ~r2_hidden(A_644, k1_relat_1(A_645)) | ~v1_relat_1(A_645) | ~v1_relat_1(A_645))), inference(superposition, [status(thm), theory('equality')], [c_48, c_5097])).
% 7.19/2.47  tff(c_3850, plain, (![A_442, B_443, C_444]: (r2_hidden(k4_tarski(A_442, '#skF_7'(A_442, B_443, C_444)), C_444) | ~r2_hidden(A_442, k10_relat_1(C_444, B_443)) | ~v1_relat_1(C_444))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.19/2.47  tff(c_3659, plain, (~m1_subset_1('#skF_12', '#skF_9')), inference(splitRight, [status(thm)], [c_76])).
% 7.19/2.47  tff(c_74, plain, (![E_89]: (~r2_hidden(k4_tarski('#skF_11', E_89), '#skF_10') | ~m1_subset_1(E_89, '#skF_9') | m1_subset_1('#skF_12', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.19/2.47  tff(c_3706, plain, (![E_89]: (~r2_hidden(k4_tarski('#skF_11', E_89), '#skF_10') | ~m1_subset_1(E_89, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_3659, c_74])).
% 7.19/2.47  tff(c_3860, plain, (![B_443]: (~m1_subset_1('#skF_7'('#skF_11', B_443, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_443)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_3850, c_3706])).
% 7.19/2.47  tff(c_3884, plain, (![B_445]: (~m1_subset_1('#skF_7'('#skF_11', B_445, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_445)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_3860])).
% 7.19/2.47  tff(c_3888, plain, (~m1_subset_1('#skF_7'('#skF_11', k2_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_48, c_3884])).
% 7.19/2.47  tff(c_3890, plain, (~m1_subset_1('#skF_7'('#skF_11', k2_relat_1('#skF_10'), '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_3736, c_3888])).
% 7.19/2.47  tff(c_7026, plain, (~v5_relat_1('#skF_10', '#skF_9') | ~r2_hidden('#skF_11', k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_7023, c_3890])).
% 7.19/2.47  tff(c_7046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_3736, c_3671, c_7026])).
% 7.19/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.19/2.47  
% 7.19/2.47  Inference rules
% 7.19/2.47  ----------------------
% 7.19/2.47  #Ref     : 0
% 7.19/2.47  #Sup     : 1550
% 7.19/2.47  #Fact    : 0
% 7.19/2.47  #Define  : 0
% 7.19/2.47  #Split   : 4
% 7.19/2.47  #Chain   : 0
% 7.19/2.47  #Close   : 0
% 7.19/2.47  
% 7.19/2.47  Ordering : KBO
% 7.19/2.47  
% 7.19/2.47  Simplification rules
% 7.19/2.47  ----------------------
% 7.19/2.47  #Subsume      : 123
% 7.19/2.47  #Demod        : 233
% 7.19/2.47  #Tautology    : 102
% 7.19/2.47  #SimpNegUnit  : 2
% 7.19/2.47  #BackRed      : 4
% 7.19/2.47  
% 7.19/2.47  #Partial instantiations: 0
% 7.19/2.47  #Strategies tried      : 1
% 7.19/2.47  
% 7.19/2.47  Timing (in seconds)
% 7.19/2.47  ----------------------
% 7.19/2.47  Preprocessing        : 0.34
% 7.19/2.47  Parsing              : 0.17
% 7.19/2.47  CNF conversion       : 0.03
% 7.19/2.47  Main loop            : 1.35
% 7.19/2.47  Inferencing          : 0.50
% 7.19/2.47  Reduction            : 0.34
% 7.19/2.47  Demodulation         : 0.24
% 7.19/2.48  BG Simplification    : 0.07
% 7.19/2.48  Subsumption          : 0.30
% 7.19/2.48  Abstraction          : 0.10
% 7.19/2.48  MUC search           : 0.00
% 7.19/2.48  Cooper               : 0.00
% 7.19/2.48  Total                : 1.73
% 7.19/2.48  Index Insertion      : 0.00
% 7.19/2.48  Index Deletion       : 0.00
% 7.19/2.48  Index Matching       : 0.00
% 7.19/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
