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
% DateTime   : Thu Dec  3 10:13:13 EST 2020

% Result     : Theorem 12.89s
% Output     : CNFRefutation 12.89s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 602 expanded)
%              Number of leaves         :   51 ( 230 expanded)
%              Depth                    :   13
%              Number of atoms          :  249 (1690 expanded)
%              Number of equality atoms :   80 ( 443 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_230,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_194,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_170,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_182,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_168,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_192,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_150,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_80,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_12,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_161,plain,(
    ! [B_77,A_78] :
      ( v1_relat_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_167,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_92,c_161])).

tff(c_176,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_167])).

tff(c_308,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_319,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_308])).

tff(c_324,plain,(
    ! [B_99,A_100] :
      ( k7_relat_1(B_99,A_100) = B_99
      | ~ v4_relat_1(B_99,A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_333,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_319,c_324])).

tff(c_342,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_333])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_355,plain,
    ( k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_16])).

tff(c_359,plain,(
    k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_355])).

tff(c_215,plain,(
    ! [B_84,A_85] :
      ( k2_relat_1(k7_relat_1(B_84,A_85)) = k9_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_72,plain,(
    ! [A_63] : k6_relat_1(A_63) = k6_partfun1(A_63) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_32,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k6_relat_1(k2_relat_1(A_29))) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_107,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k6_partfun1(k2_relat_1(A_29))) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_32])).

tff(c_8557,plain,(
    ! [B_423,A_424] :
      ( k5_relat_1(k7_relat_1(B_423,A_424),k6_partfun1(k9_relat_1(B_423,A_424))) = k7_relat_1(B_423,A_424)
      | ~ v1_relat_1(k7_relat_1(B_423,A_424))
      | ~ v1_relat_1(B_423) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_107])).

tff(c_8623,plain,
    ( k5_relat_1('#skF_4',k6_partfun1(k9_relat_1('#skF_4','#skF_2'))) = k7_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_8557])).

tff(c_8669,plain,(
    k5_relat_1('#skF_4',k6_partfun1(k2_relat_1('#skF_4'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_176,c_342,c_342,c_359,c_8623])).

tff(c_64,plain,(
    ! [A_50] : m1_subset_1(k6_relat_1(A_50),k1_zfmisc_1(k2_zfmisc_1(A_50,A_50))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_103,plain,(
    ! [A_50] : m1_subset_1(k6_partfun1(A_50),k1_zfmisc_1(k2_zfmisc_1(A_50,A_50))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64])).

tff(c_164,plain,(
    ! [A_50] :
      ( v1_relat_1(k6_partfun1(A_50))
      | ~ v1_relat_1(k2_zfmisc_1(A_50,A_50)) ) ),
    inference(resolution,[status(thm)],[c_103,c_161])).

tff(c_173,plain,(
    ! [A_50] : v1_relat_1(k6_partfun1(A_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_164])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( k5_relat_1(k6_relat_1(A_30),B_31) = k7_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_106,plain,(
    ! [A_30,B_31] :
      ( k5_relat_1(k6_partfun1(A_30),B_31) = k7_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_34])).

tff(c_4877,plain,(
    ! [A_281,B_282,C_283] :
      ( k5_relat_1(k5_relat_1(A_281,B_282),C_283) = k5_relat_1(A_281,k5_relat_1(B_282,C_283))
      | ~ v1_relat_1(C_283)
      | ~ v1_relat_1(B_282)
      | ~ v1_relat_1(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4943,plain,(
    ! [A_30,B_31,C_283] :
      ( k5_relat_1(k6_partfun1(A_30),k5_relat_1(B_31,C_283)) = k5_relat_1(k7_relat_1(B_31,A_30),C_283)
      | ~ v1_relat_1(C_283)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(k6_partfun1(A_30))
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_4877])).

tff(c_4975,plain,(
    ! [A_30,B_31,C_283] :
      ( k5_relat_1(k6_partfun1(A_30),k5_relat_1(B_31,C_283)) = k5_relat_1(k7_relat_1(B_31,A_30),C_283)
      | ~ v1_relat_1(C_283)
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_4943])).

tff(c_8682,plain,(
    ! [A_30] :
      ( k5_relat_1(k7_relat_1('#skF_4',A_30),k6_partfun1(k2_relat_1('#skF_4'))) = k5_relat_1(k6_partfun1(A_30),'#skF_4')
      | ~ v1_relat_1(k6_partfun1(k2_relat_1('#skF_4')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8669,c_4975])).

tff(c_11173,plain,(
    ! [A_466] : k5_relat_1(k7_relat_1('#skF_4',A_466),k6_partfun1(k2_relat_1('#skF_4'))) = k5_relat_1(k6_partfun1(A_466),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_173,c_8682])).

tff(c_11207,plain,(
    k5_relat_1('#skF_4',k6_partfun1(k2_relat_1('#skF_4'))) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_11173])).

tff(c_11224,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8669,c_11207])).

tff(c_98,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_170,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_98,c_161])).

tff(c_179,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_170])).

tff(c_102,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_86,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_369,plain,(
    ! [A_101] :
      ( k4_relat_1(A_101) = k2_funct_1(A_101)
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_372,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_369])).

tff(c_375,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_102,c_372])).

tff(c_90,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_594,plain,(
    ! [A_121,B_122,C_123] :
      ( k2_relset_1(A_121,B_122,C_123) = k2_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_606,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_594])).

tff(c_612,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_606])).

tff(c_632,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_107])).

tff(c_646,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_632])).

tff(c_320,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_308])).

tff(c_330,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_320,c_324])).

tff(c_339,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_330])).

tff(c_7358,plain,(
    ! [A_397,B_398,C_399] :
      ( k5_relat_1(k6_partfun1(A_397),k5_relat_1(B_398,C_399)) = k5_relat_1(k7_relat_1(B_398,A_397),C_399)
      | ~ v1_relat_1(C_399)
      | ~ v1_relat_1(B_398) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_4943])).

tff(c_7443,plain,(
    ! [A_397] :
      ( k5_relat_1(k7_relat_1('#skF_3',A_397),k6_partfun1('#skF_2')) = k5_relat_1(k6_partfun1(A_397),'#skF_3')
      | ~ v1_relat_1(k6_partfun1('#skF_2'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_7358])).

tff(c_7592,plain,(
    ! [A_403] : k5_relat_1(k7_relat_1('#skF_3',A_403),k6_partfun1('#skF_2')) = k5_relat_1(k6_partfun1(A_403),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_173,c_7443])).

tff(c_7617,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_7592])).

tff(c_7628,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_7617])).

tff(c_30,plain,(
    ! [A_28] : k4_relat_1(k6_relat_1(A_28)) = k6_relat_1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_108,plain,(
    ! [A_28] : k4_relat_1(k6_partfun1(A_28)) = k6_partfun1(A_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_30])).

tff(c_1032,plain,(
    ! [B_142,A_143] :
      ( k5_relat_1(k4_relat_1(B_142),k4_relat_1(A_143)) = k4_relat_1(k5_relat_1(A_143,B_142))
      | ~ v1_relat_1(B_142)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1044,plain,(
    ! [A_143] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k4_relat_1(A_143)) = k4_relat_1(k5_relat_1(A_143,'#skF_3'))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_1032])).

tff(c_1064,plain,(
    ! [A_144] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k4_relat_1(A_144)) = k4_relat_1(k5_relat_1(A_144,'#skF_3'))
      | ~ v1_relat_1(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_1044])).

tff(c_1079,plain,(
    ! [A_28] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_28)) = k4_relat_1(k5_relat_1(k6_partfun1(A_28),'#skF_3'))
      | ~ v1_relat_1(k6_partfun1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1064])).

tff(c_1087,plain,(
    ! [A_28] : k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_28)) = k4_relat_1(k5_relat_1(k6_partfun1(A_28),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_1079])).

tff(c_96,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_66,plain,(
    ! [B_52,E_55,F_56,C_53,D_54,A_51] :
      ( m1_subset_1(k1_partfun1(A_51,B_52,C_53,D_54,E_55,F_56),k1_zfmisc_1(k2_zfmisc_1(A_51,D_54)))
      | ~ m1_subset_1(F_56,k1_zfmisc_1(k2_zfmisc_1(C_53,D_54)))
      | ~ v1_funct_1(F_56)
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_1(E_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_88,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_5111,plain,(
    ! [D_287,C_288,A_289,B_290] :
      ( D_287 = C_288
      | ~ r2_relset_1(A_289,B_290,C_288,D_287)
      | ~ m1_subset_1(D_287,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_5121,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_88,c_5111])).

tff(c_5138,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_5121])).

tff(c_5142,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5138])).

tff(c_6057,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_5142])).

tff(c_6061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_96,c_92,c_6057])).

tff(c_6062,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5138])).

tff(c_6359,plain,(
    ! [D_361,B_357,F_359,E_358,C_362,A_360] :
      ( k1_partfun1(A_360,B_357,C_362,D_361,E_358,F_359) = k5_relat_1(E_358,F_359)
      | ~ m1_subset_1(F_359,k1_zfmisc_1(k2_zfmisc_1(C_362,D_361)))
      | ~ v1_funct_1(F_359)
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(A_360,B_357)))
      | ~ v1_funct_1(E_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_6365,plain,(
    ! [A_360,B_357,E_358] :
      ( k1_partfun1(A_360,B_357,'#skF_2','#skF_1',E_358,'#skF_4') = k5_relat_1(E_358,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(A_360,B_357)))
      | ~ v1_funct_1(E_358) ) ),
    inference(resolution,[status(thm)],[c_92,c_6359])).

tff(c_6684,plain,(
    ! [A_382,B_383,E_384] :
      ( k1_partfun1(A_382,B_383,'#skF_2','#skF_1',E_384,'#skF_4') = k5_relat_1(E_384,'#skF_4')
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(A_382,B_383)))
      | ~ v1_funct_1(E_384) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_6365])).

tff(c_6699,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_6684])).

tff(c_6708,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_6062,c_6699])).

tff(c_10,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_379,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_10])).

tff(c_383,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_379])).

tff(c_50,plain,(
    ! [A_39] :
      ( k5_relat_1(k2_funct_1(A_39),A_39) = k6_relat_1(k2_relat_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_105,plain,(
    ! [A_39] :
      ( k5_relat_1(k2_funct_1(A_39),A_39) = k6_partfun1(k2_relat_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_50])).

tff(c_15693,plain,(
    ! [A_532,C_533] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_532)),C_533) = k5_relat_1(k2_funct_1(A_532),k5_relat_1(A_532,C_533))
      | ~ v1_relat_1(C_533)
      | ~ v1_relat_1(A_532)
      | ~ v1_relat_1(k2_funct_1(A_532))
      | ~ v2_funct_1(A_532)
      | ~ v1_funct_1(A_532)
      | ~ v1_relat_1(A_532) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_4877])).

tff(c_16023,plain,(
    ! [C_533] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_533)) = k5_relat_1(k6_partfun1('#skF_2'),C_533)
      | ~ v1_relat_1(C_533)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_15693])).

tff(c_18089,plain,(
    ! [C_579] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_579)) = k5_relat_1(k6_partfun1('#skF_2'),C_579)
      | ~ v1_relat_1(C_579) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_102,c_86,c_383,c_179,c_16023])).

tff(c_18174,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6708,c_18089])).

tff(c_18230,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_11224,c_375,c_7628,c_1087,c_18174])).

tff(c_18232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_18230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.89/5.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.89/5.14  
% 12.89/5.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.89/5.14  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.89/5.14  
% 12.89/5.14  %Foreground sorts:
% 12.89/5.14  
% 12.89/5.14  
% 12.89/5.14  %Background operators:
% 12.89/5.14  
% 12.89/5.14  
% 12.89/5.14  %Foreground operators:
% 12.89/5.14  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.89/5.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.89/5.14  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.89/5.14  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.89/5.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.89/5.14  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 12.89/5.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.89/5.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.89/5.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.89/5.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.89/5.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.89/5.14  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.89/5.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.89/5.14  tff('#skF_2', type, '#skF_2': $i).
% 12.89/5.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.89/5.14  tff('#skF_3', type, '#skF_3': $i).
% 12.89/5.14  tff('#skF_1', type, '#skF_1': $i).
% 12.89/5.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.89/5.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.89/5.14  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.89/5.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.89/5.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.89/5.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.89/5.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.89/5.14  tff('#skF_4', type, '#skF_4': $i).
% 12.89/5.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.89/5.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.89/5.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.89/5.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.89/5.14  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 12.89/5.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.89/5.14  
% 12.89/5.16  tff(f_230, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 12.89/5.16  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.89/5.16  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.89/5.16  tff(f_156, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.89/5.16  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 12.89/5.16  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 12.89/5.16  tff(f_194, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.89/5.16  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 12.89/5.16  tff(f_170, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 12.89/5.16  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 12.89/5.16  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 12.89/5.16  tff(f_104, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 12.89/5.16  tff(f_160, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.89/5.16  tff(f_88, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 12.89/5.16  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 12.89/5.16  tff(f_182, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 12.89/5.16  tff(f_168, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 12.89/5.16  tff(f_192, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 12.89/5.16  tff(f_42, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 12.89/5.16  tff(f_150, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 12.89/5.16  tff(c_80, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_230])).
% 12.89/5.16  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.89/5.16  tff(c_92, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 12.89/5.16  tff(c_161, plain, (![B_77, A_78]: (v1_relat_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.89/5.16  tff(c_167, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_92, c_161])).
% 12.89/5.16  tff(c_176, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_167])).
% 12.89/5.16  tff(c_308, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 12.89/5.16  tff(c_319, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_92, c_308])).
% 12.89/5.16  tff(c_324, plain, (![B_99, A_100]: (k7_relat_1(B_99, A_100)=B_99 | ~v4_relat_1(B_99, A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.89/5.16  tff(c_333, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_319, c_324])).
% 12.89/5.16  tff(c_342, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_333])).
% 12.89/5.16  tff(c_16, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.89/5.16  tff(c_355, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_342, c_16])).
% 12.89/5.16  tff(c_359, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_355])).
% 12.89/5.16  tff(c_215, plain, (![B_84, A_85]: (k2_relat_1(k7_relat_1(B_84, A_85))=k9_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.89/5.16  tff(c_72, plain, (![A_63]: (k6_relat_1(A_63)=k6_partfun1(A_63))), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.89/5.16  tff(c_32, plain, (![A_29]: (k5_relat_1(A_29, k6_relat_1(k2_relat_1(A_29)))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.89/5.16  tff(c_107, plain, (![A_29]: (k5_relat_1(A_29, k6_partfun1(k2_relat_1(A_29)))=A_29 | ~v1_relat_1(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_32])).
% 12.89/5.16  tff(c_8557, plain, (![B_423, A_424]: (k5_relat_1(k7_relat_1(B_423, A_424), k6_partfun1(k9_relat_1(B_423, A_424)))=k7_relat_1(B_423, A_424) | ~v1_relat_1(k7_relat_1(B_423, A_424)) | ~v1_relat_1(B_423))), inference(superposition, [status(thm), theory('equality')], [c_215, c_107])).
% 12.89/5.16  tff(c_8623, plain, (k5_relat_1('#skF_4', k6_partfun1(k9_relat_1('#skF_4', '#skF_2')))=k7_relat_1('#skF_4', '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_342, c_8557])).
% 12.89/5.16  tff(c_8669, plain, (k5_relat_1('#skF_4', k6_partfun1(k2_relat_1('#skF_4')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_176, c_342, c_342, c_359, c_8623])).
% 12.89/5.16  tff(c_64, plain, (![A_50]: (m1_subset_1(k6_relat_1(A_50), k1_zfmisc_1(k2_zfmisc_1(A_50, A_50))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.89/5.16  tff(c_103, plain, (![A_50]: (m1_subset_1(k6_partfun1(A_50), k1_zfmisc_1(k2_zfmisc_1(A_50, A_50))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64])).
% 12.89/5.16  tff(c_164, plain, (![A_50]: (v1_relat_1(k6_partfun1(A_50)) | ~v1_relat_1(k2_zfmisc_1(A_50, A_50)))), inference(resolution, [status(thm)], [c_103, c_161])).
% 12.89/5.16  tff(c_173, plain, (![A_50]: (v1_relat_1(k6_partfun1(A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_164])).
% 12.89/5.16  tff(c_34, plain, (![A_30, B_31]: (k5_relat_1(k6_relat_1(A_30), B_31)=k7_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.89/5.16  tff(c_106, plain, (![A_30, B_31]: (k5_relat_1(k6_partfun1(A_30), B_31)=k7_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_34])).
% 12.89/5.16  tff(c_4877, plain, (![A_281, B_282, C_283]: (k5_relat_1(k5_relat_1(A_281, B_282), C_283)=k5_relat_1(A_281, k5_relat_1(B_282, C_283)) | ~v1_relat_1(C_283) | ~v1_relat_1(B_282) | ~v1_relat_1(A_281))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.89/5.16  tff(c_4943, plain, (![A_30, B_31, C_283]: (k5_relat_1(k6_partfun1(A_30), k5_relat_1(B_31, C_283))=k5_relat_1(k7_relat_1(B_31, A_30), C_283) | ~v1_relat_1(C_283) | ~v1_relat_1(B_31) | ~v1_relat_1(k6_partfun1(A_30)) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_106, c_4877])).
% 12.89/5.16  tff(c_4975, plain, (![A_30, B_31, C_283]: (k5_relat_1(k6_partfun1(A_30), k5_relat_1(B_31, C_283))=k5_relat_1(k7_relat_1(B_31, A_30), C_283) | ~v1_relat_1(C_283) | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_4943])).
% 12.89/5.16  tff(c_8682, plain, (![A_30]: (k5_relat_1(k7_relat_1('#skF_4', A_30), k6_partfun1(k2_relat_1('#skF_4')))=k5_relat_1(k6_partfun1(A_30), '#skF_4') | ~v1_relat_1(k6_partfun1(k2_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8669, c_4975])).
% 12.89/5.16  tff(c_11173, plain, (![A_466]: (k5_relat_1(k7_relat_1('#skF_4', A_466), k6_partfun1(k2_relat_1('#skF_4')))=k5_relat_1(k6_partfun1(A_466), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_173, c_8682])).
% 12.89/5.16  tff(c_11207, plain, (k5_relat_1('#skF_4', k6_partfun1(k2_relat_1('#skF_4')))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_342, c_11173])).
% 12.89/5.16  tff(c_11224, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8669, c_11207])).
% 12.89/5.16  tff(c_98, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 12.89/5.16  tff(c_170, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_98, c_161])).
% 12.89/5.16  tff(c_179, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_170])).
% 12.89/5.16  tff(c_102, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 12.89/5.16  tff(c_86, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 12.89/5.16  tff(c_369, plain, (![A_101]: (k4_relat_1(A_101)=k2_funct_1(A_101) | ~v2_funct_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.89/5.16  tff(c_372, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_369])).
% 12.89/5.16  tff(c_375, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_102, c_372])).
% 12.89/5.16  tff(c_90, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_230])).
% 12.89/5.16  tff(c_594, plain, (![A_121, B_122, C_123]: (k2_relset_1(A_121, B_122, C_123)=k2_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 12.89/5.16  tff(c_606, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_594])).
% 12.89/5.16  tff(c_612, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_606])).
% 12.89/5.16  tff(c_632, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_612, c_107])).
% 12.89/5.16  tff(c_646, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_632])).
% 12.89/5.16  tff(c_320, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_98, c_308])).
% 12.89/5.16  tff(c_330, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_320, c_324])).
% 12.89/5.16  tff(c_339, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_330])).
% 12.89/5.16  tff(c_7358, plain, (![A_397, B_398, C_399]: (k5_relat_1(k6_partfun1(A_397), k5_relat_1(B_398, C_399))=k5_relat_1(k7_relat_1(B_398, A_397), C_399) | ~v1_relat_1(C_399) | ~v1_relat_1(B_398))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_4943])).
% 12.89/5.16  tff(c_7443, plain, (![A_397]: (k5_relat_1(k7_relat_1('#skF_3', A_397), k6_partfun1('#skF_2'))=k5_relat_1(k6_partfun1(A_397), '#skF_3') | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_646, c_7358])).
% 12.89/5.16  tff(c_7592, plain, (![A_403]: (k5_relat_1(k7_relat_1('#skF_3', A_403), k6_partfun1('#skF_2'))=k5_relat_1(k6_partfun1(A_403), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_173, c_7443])).
% 12.89/5.16  tff(c_7617, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_339, c_7592])).
% 12.89/5.16  tff(c_7628, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_646, c_7617])).
% 12.89/5.16  tff(c_30, plain, (![A_28]: (k4_relat_1(k6_relat_1(A_28))=k6_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.89/5.16  tff(c_108, plain, (![A_28]: (k4_relat_1(k6_partfun1(A_28))=k6_partfun1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_30])).
% 12.89/5.16  tff(c_1032, plain, (![B_142, A_143]: (k5_relat_1(k4_relat_1(B_142), k4_relat_1(A_143))=k4_relat_1(k5_relat_1(A_143, B_142)) | ~v1_relat_1(B_142) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.89/5.16  tff(c_1044, plain, (![A_143]: (k5_relat_1(k2_funct_1('#skF_3'), k4_relat_1(A_143))=k4_relat_1(k5_relat_1(A_143, '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_143))), inference(superposition, [status(thm), theory('equality')], [c_375, c_1032])).
% 12.89/5.16  tff(c_1064, plain, (![A_144]: (k5_relat_1(k2_funct_1('#skF_3'), k4_relat_1(A_144))=k4_relat_1(k5_relat_1(A_144, '#skF_3')) | ~v1_relat_1(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_1044])).
% 12.89/5.16  tff(c_1079, plain, (![A_28]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_28))=k4_relat_1(k5_relat_1(k6_partfun1(A_28), '#skF_3')) | ~v1_relat_1(k6_partfun1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1064])).
% 12.89/5.16  tff(c_1087, plain, (![A_28]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_28))=k4_relat_1(k5_relat_1(k6_partfun1(A_28), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_1079])).
% 12.89/5.16  tff(c_96, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 12.89/5.16  tff(c_66, plain, (![B_52, E_55, F_56, C_53, D_54, A_51]: (m1_subset_1(k1_partfun1(A_51, B_52, C_53, D_54, E_55, F_56), k1_zfmisc_1(k2_zfmisc_1(A_51, D_54))) | ~m1_subset_1(F_56, k1_zfmisc_1(k2_zfmisc_1(C_53, D_54))) | ~v1_funct_1(F_56) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_1(E_55))), inference(cnfTransformation, [status(thm)], [f_182])).
% 12.89/5.16  tff(c_88, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 12.89/5.16  tff(c_5111, plain, (![D_287, C_288, A_289, B_290]: (D_287=C_288 | ~r2_relset_1(A_289, B_290, C_288, D_287) | ~m1_subset_1(D_287, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))))), inference(cnfTransformation, [status(thm)], [f_168])).
% 12.89/5.16  tff(c_5121, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_88, c_5111])).
% 12.89/5.16  tff(c_5138, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_5121])).
% 12.89/5.16  tff(c_5142, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5138])).
% 12.89/5.16  tff(c_6057, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_5142])).
% 12.89/5.16  tff(c_6061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_96, c_92, c_6057])).
% 12.89/5.16  tff(c_6062, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5138])).
% 12.89/5.16  tff(c_6359, plain, (![D_361, B_357, F_359, E_358, C_362, A_360]: (k1_partfun1(A_360, B_357, C_362, D_361, E_358, F_359)=k5_relat_1(E_358, F_359) | ~m1_subset_1(F_359, k1_zfmisc_1(k2_zfmisc_1(C_362, D_361))) | ~v1_funct_1(F_359) | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(A_360, B_357))) | ~v1_funct_1(E_358))), inference(cnfTransformation, [status(thm)], [f_192])).
% 12.89/5.16  tff(c_6365, plain, (![A_360, B_357, E_358]: (k1_partfun1(A_360, B_357, '#skF_2', '#skF_1', E_358, '#skF_4')=k5_relat_1(E_358, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(A_360, B_357))) | ~v1_funct_1(E_358))), inference(resolution, [status(thm)], [c_92, c_6359])).
% 12.89/5.16  tff(c_6684, plain, (![A_382, B_383, E_384]: (k1_partfun1(A_382, B_383, '#skF_2', '#skF_1', E_384, '#skF_4')=k5_relat_1(E_384, '#skF_4') | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(A_382, B_383))) | ~v1_funct_1(E_384))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_6365])).
% 12.89/5.16  tff(c_6699, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_6684])).
% 12.89/5.16  tff(c_6708, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_6062, c_6699])).
% 12.89/5.16  tff(c_10, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.89/5.16  tff(c_379, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_375, c_10])).
% 12.89/5.16  tff(c_383, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_379])).
% 12.89/5.16  tff(c_50, plain, (![A_39]: (k5_relat_1(k2_funct_1(A_39), A_39)=k6_relat_1(k2_relat_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.89/5.16  tff(c_105, plain, (![A_39]: (k5_relat_1(k2_funct_1(A_39), A_39)=k6_partfun1(k2_relat_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_50])).
% 12.89/5.16  tff(c_15693, plain, (![A_532, C_533]: (k5_relat_1(k6_partfun1(k2_relat_1(A_532)), C_533)=k5_relat_1(k2_funct_1(A_532), k5_relat_1(A_532, C_533)) | ~v1_relat_1(C_533) | ~v1_relat_1(A_532) | ~v1_relat_1(k2_funct_1(A_532)) | ~v2_funct_1(A_532) | ~v1_funct_1(A_532) | ~v1_relat_1(A_532))), inference(superposition, [status(thm), theory('equality')], [c_105, c_4877])).
% 12.89/5.16  tff(c_16023, plain, (![C_533]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_533))=k5_relat_1(k6_partfun1('#skF_2'), C_533) | ~v1_relat_1(C_533) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_612, c_15693])).
% 12.89/5.16  tff(c_18089, plain, (![C_579]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_579))=k5_relat_1(k6_partfun1('#skF_2'), C_579) | ~v1_relat_1(C_579))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_102, c_86, c_383, c_179, c_16023])).
% 12.89/5.16  tff(c_18174, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6708, c_18089])).
% 12.89/5.16  tff(c_18230, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_11224, c_375, c_7628, c_1087, c_18174])).
% 12.89/5.16  tff(c_18232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_18230])).
% 12.89/5.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.89/5.16  
% 12.89/5.16  Inference rules
% 12.89/5.16  ----------------------
% 12.89/5.16  #Ref     : 0
% 12.89/5.16  #Sup     : 3959
% 12.89/5.16  #Fact    : 0
% 12.89/5.16  #Define  : 0
% 12.89/5.16  #Split   : 16
% 12.89/5.16  #Chain   : 0
% 12.89/5.16  #Close   : 0
% 12.89/5.16  
% 12.89/5.16  Ordering : KBO
% 12.89/5.16  
% 12.89/5.16  Simplification rules
% 12.89/5.16  ----------------------
% 12.89/5.16  #Subsume      : 121
% 12.89/5.16  #Demod        : 6933
% 12.89/5.16  #Tautology    : 1476
% 12.89/5.16  #SimpNegUnit  : 2
% 12.89/5.16  #BackRed      : 73
% 12.89/5.16  
% 12.89/5.16  #Partial instantiations: 0
% 12.89/5.16  #Strategies tried      : 1
% 12.89/5.16  
% 12.89/5.16  Timing (in seconds)
% 12.89/5.16  ----------------------
% 12.89/5.16  Preprocessing        : 0.41
% 12.89/5.16  Parsing              : 0.22
% 12.89/5.16  CNF conversion       : 0.03
% 12.89/5.16  Main loop            : 3.98
% 12.89/5.16  Inferencing          : 0.96
% 12.89/5.16  Reduction            : 2.03
% 12.89/5.16  Demodulation         : 1.72
% 12.89/5.17  BG Simplification    : 0.10
% 12.89/5.17  Subsumption          : 0.68
% 12.89/5.17  Abstraction          : 0.13
% 12.89/5.17  MUC search           : 0.00
% 12.89/5.17  Cooper               : 0.00
% 12.89/5.17  Total                : 4.43
% 12.89/5.17  Index Insertion      : 0.00
% 12.89/5.17  Index Deletion       : 0.00
% 12.89/5.17  Index Matching       : 0.00
% 12.89/5.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
