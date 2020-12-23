%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:07 EST 2020

% Result     : Theorem 8.51s
% Output     : CNFRefutation 8.51s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 228 expanded)
%              Number of leaves         :   43 (  98 expanded)
%              Depth                    :   10
%              Number of atoms          :  165 ( 506 expanded)
%              Number of equality atoms :   12 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_13 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_109,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10123,plain,(
    ! [A_888,B_889,C_890] :
      ( k2_relset_1(A_888,B_889,C_890) = k2_relat_1(C_890)
      | ~ m1_subset_1(C_890,k1_zfmisc_1(k2_zfmisc_1(A_888,B_889))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10127,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_10123])).

tff(c_42,plain,(
    ! [A_35,B_36] : v1_relat_1(k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_90,plain,(
    ! [B_102,A_103] :
      ( v1_relat_1(B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_103))
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_60,c_90])).

tff(c_96,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_93])).

tff(c_3309,plain,(
    ! [A_371,B_372,C_373] :
      ( k2_relset_1(A_371,B_372,C_373) = k2_relat_1(C_373)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_371,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3313,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_3309])).

tff(c_76,plain,
    ( m1_subset_1('#skF_12','#skF_9')
    | r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_97,plain,(
    r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_3315,plain,(
    r2_hidden('#skF_13',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3313,c_97])).

tff(c_109,plain,(
    ! [C_113,A_114,B_115] :
      ( v4_relat_1(C_113,A_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_113,plain,(
    v4_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_109])).

tff(c_52,plain,(
    ! [A_43] :
      ( k9_relat_1(A_43,k1_relat_1(A_43)) = k2_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6813,plain,(
    ! [A_635,B_636,C_637] :
      ( r2_hidden('#skF_7'(A_635,B_636,C_637),k1_relat_1(C_637))
      | ~ r2_hidden(A_635,k9_relat_1(C_637,B_636))
      | ~ v1_relat_1(C_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_116,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(k1_relat_1(B_118),A_119)
      | ~ v4_relat_1(B_118,A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3326,plain,(
    ! [B_374,A_375] :
      ( k3_xboole_0(k1_relat_1(B_374),A_375) = k1_relat_1(B_374)
      | ~ v4_relat_1(B_374,A_375)
      | ~ v1_relat_1(B_374) ) ),
    inference(resolution,[status(thm)],[c_116,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3335,plain,(
    ! [D_6,A_375,B_374] :
      ( r2_hidden(D_6,A_375)
      | ~ r2_hidden(D_6,k1_relat_1(B_374))
      | ~ v4_relat_1(B_374,A_375)
      | ~ v1_relat_1(B_374) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3326,c_4])).

tff(c_8170,plain,(
    ! [A_744,B_745,C_746,A_747] :
      ( r2_hidden('#skF_7'(A_744,B_745,C_746),A_747)
      | ~ v4_relat_1(C_746,A_747)
      | ~ r2_hidden(A_744,k9_relat_1(C_746,B_745))
      | ~ v1_relat_1(C_746) ) ),
    inference(resolution,[status(thm)],[c_6813,c_3335])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8224,plain,(
    ! [A_750,B_751,C_752,A_753] :
      ( m1_subset_1('#skF_7'(A_750,B_751,C_752),A_753)
      | ~ v4_relat_1(C_752,A_753)
      | ~ r2_hidden(A_750,k9_relat_1(C_752,B_751))
      | ~ v1_relat_1(C_752) ) ),
    inference(resolution,[status(thm)],[c_8170,c_22])).

tff(c_10021,plain,(
    ! [A_861,A_862,A_863] :
      ( m1_subset_1('#skF_7'(A_861,k1_relat_1(A_862),A_862),A_863)
      | ~ v4_relat_1(A_862,A_863)
      | ~ r2_hidden(A_861,k2_relat_1(A_862))
      | ~ v1_relat_1(A_862)
      | ~ v1_relat_1(A_862) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_8224])).

tff(c_6827,plain,(
    ! [A_644,B_645,C_646] :
      ( r2_hidden(k4_tarski('#skF_7'(A_644,B_645,C_646),A_644),C_646)
      | ~ r2_hidden(A_644,k9_relat_1(C_646,B_645))
      | ~ v1_relat_1(C_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3439,plain,(
    ! [A_395,B_396,C_397] :
      ( r2_hidden('#skF_7'(A_395,B_396,C_397),k1_relat_1(C_397))
      | ~ r2_hidden(A_395,k9_relat_1(C_397,B_396))
      | ~ v1_relat_1(C_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4567,plain,(
    ! [A_495,B_496,C_497,A_498] :
      ( r2_hidden('#skF_7'(A_495,B_496,C_497),A_498)
      | ~ v4_relat_1(C_497,A_498)
      | ~ r2_hidden(A_495,k9_relat_1(C_497,B_496))
      | ~ v1_relat_1(C_497) ) ),
    inference(resolution,[status(thm)],[c_3439,c_3335])).

tff(c_4719,plain,(
    ! [A_509,B_510,C_511,A_512] :
      ( m1_subset_1('#skF_7'(A_509,B_510,C_511),A_512)
      | ~ v4_relat_1(C_511,A_512)
      | ~ r2_hidden(A_509,k9_relat_1(C_511,B_510))
      | ~ v1_relat_1(C_511) ) ),
    inference(resolution,[status(thm)],[c_4567,c_22])).

tff(c_6686,plain,(
    ! [A_619,A_620,A_621] :
      ( m1_subset_1('#skF_7'(A_619,k1_relat_1(A_620),A_620),A_621)
      | ~ v4_relat_1(A_620,A_621)
      | ~ r2_hidden(A_619,k2_relat_1(A_620))
      | ~ v1_relat_1(A_620)
      | ~ v1_relat_1(A_620) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4719])).

tff(c_3448,plain,(
    ! [A_401,B_402,C_403] :
      ( r2_hidden(k4_tarski('#skF_7'(A_401,B_402,C_403),A_401),C_403)
      | ~ r2_hidden(A_401,k9_relat_1(C_403,B_402))
      | ~ v1_relat_1(C_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    ! [E_91] :
      ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10')
      | ~ r2_hidden(k4_tarski(E_91,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_91,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3349,plain,(
    ! [E_91] :
      ( ~ r2_hidden(k4_tarski(E_91,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_91,'#skF_9') ) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_3455,plain,(
    ! [B_402] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_402,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_402))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_3448,c_3349])).

tff(c_3506,plain,(
    ! [B_410] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_410,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_410)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3455])).

tff(c_3510,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_13',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_3506])).

tff(c_3512,plain,(
    ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3315,c_3510])).

tff(c_6689,plain,
    ( ~ v4_relat_1('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_13',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_6686,c_3512])).

tff(c_6709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3315,c_113,c_6689])).

tff(c_6710,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_32,plain,(
    ! [C_31,A_16,D_34] :
      ( r2_hidden(C_31,k2_relat_1(A_16))
      | ~ r2_hidden(k4_tarski(D_34,C_31),A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6717,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_6710,c_32])).

tff(c_66,plain,(
    ! [E_91] :
      ( ~ r2_hidden('#skF_11',k2_relset_1('#skF_9','#skF_8','#skF_10'))
      | ~ r2_hidden(k4_tarski(E_91,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_91,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6743,plain,(
    ! [E_91] :
      ( ~ r2_hidden(k4_tarski(E_91,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_91,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6717,c_3313,c_66])).

tff(c_6834,plain,(
    ! [B_645] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_645,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_645))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_6827,c_6743])).

tff(c_6861,plain,(
    ! [B_647] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_647,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_647)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_6834])).

tff(c_6865,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_13',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_6861])).

tff(c_6867,plain,(
    ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3315,c_6865])).

tff(c_10024,plain,
    ( ~ v4_relat_1('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_13',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_10021,c_6867])).

tff(c_10044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3315,c_113,c_10024])).

tff(c_10046,plain,(
    ~ r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_10128,plain,(
    ~ r2_hidden('#skF_13',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10127,c_10046])).

tff(c_74,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10')
    | r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10053,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_10046,c_74])).

tff(c_10073,plain,(
    ! [C_877,A_878,D_879] :
      ( r2_hidden(C_877,k2_relat_1(A_878))
      | ~ r2_hidden(k4_tarski(D_879,C_877),A_878) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10077,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_10053,c_10073])).

tff(c_72,plain,
    ( ~ r2_hidden('#skF_11',k2_relset_1('#skF_9','#skF_8','#skF_10'))
    | r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10134,plain,(
    r2_hidden('#skF_13',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10127,c_10077,c_10127,c_72])).

tff(c_10135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10128,c_10134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:45:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.51/2.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.51/2.98  
% 8.51/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.51/2.99  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_13 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_12 > #skF_4
% 8.51/2.99  
% 8.51/2.99  %Foreground sorts:
% 8.51/2.99  
% 8.51/2.99  
% 8.51/2.99  %Background operators:
% 8.51/2.99  
% 8.51/2.99  
% 8.51/2.99  %Foreground operators:
% 8.51/2.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.51/2.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.51/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.51/2.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.51/2.99  tff('#skF_11', type, '#skF_11': $i).
% 8.51/2.99  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.51/2.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.51/2.99  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.51/2.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.51/2.99  tff('#skF_10', type, '#skF_10': $i).
% 8.51/2.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.51/2.99  tff('#skF_13', type, '#skF_13': $i).
% 8.51/2.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.51/2.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.51/2.99  tff('#skF_9', type, '#skF_9': $i).
% 8.51/2.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.51/2.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.51/2.99  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 8.51/2.99  tff('#skF_8', type, '#skF_8': $i).
% 8.51/2.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.51/2.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.51/2.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.51/2.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.51/2.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.51/2.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.51/2.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.51/2.99  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.51/2.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.51/2.99  tff('#skF_12', type, '#skF_12': $i).
% 8.51/2.99  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.51/2.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.51/2.99  
% 8.51/3.01  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 8.51/3.01  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.51/3.01  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.51/3.01  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.51/3.01  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.51/3.01  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 8.51/3.01  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 8.51/3.01  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.51/3.01  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.51/3.01  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.51/3.01  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 8.51/3.01  tff(f_63, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 8.51/3.01  tff(c_60, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.51/3.01  tff(c_10123, plain, (![A_888, B_889, C_890]: (k2_relset_1(A_888, B_889, C_890)=k2_relat_1(C_890) | ~m1_subset_1(C_890, k1_zfmisc_1(k2_zfmisc_1(A_888, B_889))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.51/3.01  tff(c_10127, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_10123])).
% 8.51/3.01  tff(c_42, plain, (![A_35, B_36]: (v1_relat_1(k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.51/3.01  tff(c_90, plain, (![B_102, A_103]: (v1_relat_1(B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_103)) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.51/3.01  tff(c_93, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_60, c_90])).
% 8.51/3.01  tff(c_96, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_93])).
% 8.51/3.01  tff(c_3309, plain, (![A_371, B_372, C_373]: (k2_relset_1(A_371, B_372, C_373)=k2_relat_1(C_373) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_371, B_372))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.51/3.01  tff(c_3313, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_3309])).
% 8.51/3.01  tff(c_76, plain, (m1_subset_1('#skF_12', '#skF_9') | r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.51/3.01  tff(c_97, plain, (r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(splitLeft, [status(thm)], [c_76])).
% 8.51/3.01  tff(c_3315, plain, (r2_hidden('#skF_13', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_3313, c_97])).
% 8.51/3.01  tff(c_109, plain, (![C_113, A_114, B_115]: (v4_relat_1(C_113, A_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.51/3.01  tff(c_113, plain, (v4_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_60, c_109])).
% 8.51/3.01  tff(c_52, plain, (![A_43]: (k9_relat_1(A_43, k1_relat_1(A_43))=k2_relat_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.51/3.01  tff(c_6813, plain, (![A_635, B_636, C_637]: (r2_hidden('#skF_7'(A_635, B_636, C_637), k1_relat_1(C_637)) | ~r2_hidden(A_635, k9_relat_1(C_637, B_636)) | ~v1_relat_1(C_637))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.51/3.01  tff(c_116, plain, (![B_118, A_119]: (r1_tarski(k1_relat_1(B_118), A_119) | ~v4_relat_1(B_118, A_119) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.51/3.01  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.51/3.01  tff(c_3326, plain, (![B_374, A_375]: (k3_xboole_0(k1_relat_1(B_374), A_375)=k1_relat_1(B_374) | ~v4_relat_1(B_374, A_375) | ~v1_relat_1(B_374))), inference(resolution, [status(thm)], [c_116, c_20])).
% 8.51/3.01  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.51/3.01  tff(c_3335, plain, (![D_6, A_375, B_374]: (r2_hidden(D_6, A_375) | ~r2_hidden(D_6, k1_relat_1(B_374)) | ~v4_relat_1(B_374, A_375) | ~v1_relat_1(B_374))), inference(superposition, [status(thm), theory('equality')], [c_3326, c_4])).
% 8.51/3.01  tff(c_8170, plain, (![A_744, B_745, C_746, A_747]: (r2_hidden('#skF_7'(A_744, B_745, C_746), A_747) | ~v4_relat_1(C_746, A_747) | ~r2_hidden(A_744, k9_relat_1(C_746, B_745)) | ~v1_relat_1(C_746))), inference(resolution, [status(thm)], [c_6813, c_3335])).
% 8.51/3.01  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.51/3.01  tff(c_8224, plain, (![A_750, B_751, C_752, A_753]: (m1_subset_1('#skF_7'(A_750, B_751, C_752), A_753) | ~v4_relat_1(C_752, A_753) | ~r2_hidden(A_750, k9_relat_1(C_752, B_751)) | ~v1_relat_1(C_752))), inference(resolution, [status(thm)], [c_8170, c_22])).
% 8.51/3.01  tff(c_10021, plain, (![A_861, A_862, A_863]: (m1_subset_1('#skF_7'(A_861, k1_relat_1(A_862), A_862), A_863) | ~v4_relat_1(A_862, A_863) | ~r2_hidden(A_861, k2_relat_1(A_862)) | ~v1_relat_1(A_862) | ~v1_relat_1(A_862))), inference(superposition, [status(thm), theory('equality')], [c_52, c_8224])).
% 8.51/3.01  tff(c_6827, plain, (![A_644, B_645, C_646]: (r2_hidden(k4_tarski('#skF_7'(A_644, B_645, C_646), A_644), C_646) | ~r2_hidden(A_644, k9_relat_1(C_646, B_645)) | ~v1_relat_1(C_646))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.51/3.01  tff(c_3439, plain, (![A_395, B_396, C_397]: (r2_hidden('#skF_7'(A_395, B_396, C_397), k1_relat_1(C_397)) | ~r2_hidden(A_395, k9_relat_1(C_397, B_396)) | ~v1_relat_1(C_397))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.51/3.01  tff(c_4567, plain, (![A_495, B_496, C_497, A_498]: (r2_hidden('#skF_7'(A_495, B_496, C_497), A_498) | ~v4_relat_1(C_497, A_498) | ~r2_hidden(A_495, k9_relat_1(C_497, B_496)) | ~v1_relat_1(C_497))), inference(resolution, [status(thm)], [c_3439, c_3335])).
% 8.51/3.01  tff(c_4719, plain, (![A_509, B_510, C_511, A_512]: (m1_subset_1('#skF_7'(A_509, B_510, C_511), A_512) | ~v4_relat_1(C_511, A_512) | ~r2_hidden(A_509, k9_relat_1(C_511, B_510)) | ~v1_relat_1(C_511))), inference(resolution, [status(thm)], [c_4567, c_22])).
% 8.51/3.01  tff(c_6686, plain, (![A_619, A_620, A_621]: (m1_subset_1('#skF_7'(A_619, k1_relat_1(A_620), A_620), A_621) | ~v4_relat_1(A_620, A_621) | ~r2_hidden(A_619, k2_relat_1(A_620)) | ~v1_relat_1(A_620) | ~v1_relat_1(A_620))), inference(superposition, [status(thm), theory('equality')], [c_52, c_4719])).
% 8.51/3.01  tff(c_3448, plain, (![A_401, B_402, C_403]: (r2_hidden(k4_tarski('#skF_7'(A_401, B_402, C_403), A_401), C_403) | ~r2_hidden(A_401, k9_relat_1(C_403, B_402)) | ~v1_relat_1(C_403))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.51/3.01  tff(c_68, plain, (![E_91]: (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10') | ~r2_hidden(k4_tarski(E_91, '#skF_13'), '#skF_10') | ~m1_subset_1(E_91, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.51/3.01  tff(c_3349, plain, (![E_91]: (~r2_hidden(k4_tarski(E_91, '#skF_13'), '#skF_10') | ~m1_subset_1(E_91, '#skF_9'))), inference(splitLeft, [status(thm)], [c_68])).
% 8.51/3.01  tff(c_3455, plain, (![B_402]: (~m1_subset_1('#skF_7'('#skF_13', B_402, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_402)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_3448, c_3349])).
% 8.51/3.01  tff(c_3506, plain, (![B_410]: (~m1_subset_1('#skF_7'('#skF_13', B_410, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_410)))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_3455])).
% 8.51/3.01  tff(c_3510, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_52, c_3506])).
% 8.51/3.01  tff(c_3512, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_3315, c_3510])).
% 8.51/3.01  tff(c_6689, plain, (~v4_relat_1('#skF_10', '#skF_9') | ~r2_hidden('#skF_13', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_6686, c_3512])).
% 8.51/3.01  tff(c_6709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_3315, c_113, c_6689])).
% 8.51/3.01  tff(c_6710, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(splitRight, [status(thm)], [c_68])).
% 8.51/3.01  tff(c_32, plain, (![C_31, A_16, D_34]: (r2_hidden(C_31, k2_relat_1(A_16)) | ~r2_hidden(k4_tarski(D_34, C_31), A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.51/3.01  tff(c_6717, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_6710, c_32])).
% 8.51/3.01  tff(c_66, plain, (![E_91]: (~r2_hidden('#skF_11', k2_relset_1('#skF_9', '#skF_8', '#skF_10')) | ~r2_hidden(k4_tarski(E_91, '#skF_13'), '#skF_10') | ~m1_subset_1(E_91, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.51/3.01  tff(c_6743, plain, (![E_91]: (~r2_hidden(k4_tarski(E_91, '#skF_13'), '#skF_10') | ~m1_subset_1(E_91, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_6717, c_3313, c_66])).
% 8.51/3.01  tff(c_6834, plain, (![B_645]: (~m1_subset_1('#skF_7'('#skF_13', B_645, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_645)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_6827, c_6743])).
% 8.51/3.01  tff(c_6861, plain, (![B_647]: (~m1_subset_1('#skF_7'('#skF_13', B_647, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_647)))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_6834])).
% 8.51/3.01  tff(c_6865, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_52, c_6861])).
% 8.51/3.01  tff(c_6867, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_3315, c_6865])).
% 8.51/3.01  tff(c_10024, plain, (~v4_relat_1('#skF_10', '#skF_9') | ~r2_hidden('#skF_13', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_10021, c_6867])).
% 8.51/3.01  tff(c_10044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_3315, c_113, c_10024])).
% 8.51/3.01  tff(c_10046, plain, (~r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(splitRight, [status(thm)], [c_76])).
% 8.51/3.01  tff(c_10128, plain, (~r2_hidden('#skF_13', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_10127, c_10046])).
% 8.51/3.01  tff(c_74, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10') | r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.51/3.01  tff(c_10053, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_10046, c_74])).
% 8.51/3.01  tff(c_10073, plain, (![C_877, A_878, D_879]: (r2_hidden(C_877, k2_relat_1(A_878)) | ~r2_hidden(k4_tarski(D_879, C_877), A_878))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.51/3.01  tff(c_10077, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_10053, c_10073])).
% 8.51/3.01  tff(c_72, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_9', '#skF_8', '#skF_10')) | r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.51/3.01  tff(c_10134, plain, (r2_hidden('#skF_13', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_10127, c_10077, c_10127, c_72])).
% 8.51/3.01  tff(c_10135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10128, c_10134])).
% 8.51/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.51/3.01  
% 8.51/3.01  Inference rules
% 8.51/3.01  ----------------------
% 8.51/3.01  #Ref     : 0
% 8.51/3.01  #Sup     : 2241
% 8.51/3.01  #Fact    : 0
% 8.51/3.01  #Define  : 0
% 8.51/3.01  #Split   : 7
% 8.51/3.01  #Chain   : 0
% 8.51/3.01  #Close   : 0
% 8.51/3.01  
% 8.51/3.01  Ordering : KBO
% 8.51/3.01  
% 8.51/3.01  Simplification rules
% 8.51/3.01  ----------------------
% 8.51/3.01  #Subsume      : 184
% 8.51/3.01  #Demod        : 358
% 8.51/3.01  #Tautology    : 146
% 8.51/3.01  #SimpNegUnit  : 2
% 8.51/3.01  #BackRed      : 5
% 8.51/3.01  
% 8.51/3.01  #Partial instantiations: 0
% 8.51/3.01  #Strategies tried      : 1
% 8.51/3.01  
% 8.51/3.01  Timing (in seconds)
% 8.51/3.01  ----------------------
% 8.51/3.01  Preprocessing        : 0.35
% 8.51/3.01  Parsing              : 0.18
% 8.51/3.01  CNF conversion       : 0.03
% 8.51/3.01  Main loop            : 1.83
% 8.51/3.01  Inferencing          : 0.66
% 8.51/3.01  Reduction            : 0.47
% 8.51/3.01  Demodulation         : 0.31
% 8.51/3.01  BG Simplification    : 0.10
% 8.51/3.01  Subsumption          : 0.43
% 8.51/3.01  Abstraction          : 0.12
% 8.51/3.01  MUC search           : 0.00
% 8.51/3.01  Cooper               : 0.00
% 8.51/3.01  Total                : 2.22
% 8.51/3.01  Index Insertion      : 0.00
% 8.51/3.01  Index Deletion       : 0.00
% 8.51/3.01  Index Matching       : 0.00
% 8.51/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
