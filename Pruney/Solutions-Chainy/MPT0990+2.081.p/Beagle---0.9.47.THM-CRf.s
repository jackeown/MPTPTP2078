%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:07 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 8.23s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 921 expanded)
%              Number of leaves         :   43 ( 344 expanded)
%              Depth                    :   17
%              Number of atoms          :  448 (3939 expanded)
%              Number of equality atoms :  145 (1265 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_250,negated_conjecture,(
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

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_208,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_149,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_147,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_125,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_192,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_166,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_224,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_72,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_88,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_86,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_211,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_225,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_211])).

tff(c_351,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_funct_1(k2_funct_1(C_91))
      | k2_relset_1(A_92,B_93,C_91) != B_93
      | ~ v2_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_2(C_91,A_92,B_93)
      | ~ v1_funct_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_360,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_351])).

tff(c_369,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_225,c_360])).

tff(c_370,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_94,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_92,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_90,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_50,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_12,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_101,plain,(
    ! [A_4] : v1_relat_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12])).

tff(c_14,plain,(
    ! [A_4] : v1_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_100,plain,(
    ! [A_4] : v1_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    ! [A_1] : k1_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k6_relat_1(k2_relat_1(A_2))) = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [A_67] :
      ( k5_relat_1(A_67,k6_partfun1(k2_relat_1(A_67))) = A_67
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6])).

tff(c_164,plain,(
    ! [A_1] :
      ( k5_relat_1(k6_partfun1(A_1),k6_partfun1(A_1)) = k6_partfun1(A_1)
      | ~ v1_relat_1(k6_partfun1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_155])).

tff(c_168,plain,(
    ! [A_1] : k5_relat_1(k6_partfun1(A_1),k6_partfun1(A_1)) = k6_partfun1(A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_164])).

tff(c_22,plain,(
    ! [A_6,B_8] :
      ( v2_funct_1(A_6)
      | k6_relat_1(k1_relat_1(A_6)) != k5_relat_1(A_6,B_8)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_294,plain,(
    ! [A_86,B_87] :
      ( v2_funct_1(A_86)
      | k6_partfun1(k1_relat_1(A_86)) != k5_relat_1(A_86,B_87)
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_22])).

tff(c_304,plain,(
    ! [A_1] :
      ( v2_funct_1(k6_partfun1(A_1))
      | k6_partfun1(k1_relat_1(k6_partfun1(A_1))) != k6_partfun1(A_1)
      | ~ v1_funct_1(k6_partfun1(A_1))
      | ~ v1_relat_1(k6_partfun1(A_1))
      | ~ v1_funct_1(k6_partfun1(A_1))
      | ~ v1_relat_1(k6_partfun1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_294])).

tff(c_313,plain,(
    ! [A_1] : v2_funct_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_100,c_101,c_100,c_104,c_304])).

tff(c_82,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_743,plain,(
    ! [A_143,C_145,E_142,B_141,F_144,D_140] :
      ( k1_partfun1(A_143,B_141,C_145,D_140,E_142,F_144) = k5_relat_1(E_142,F_144)
      | ~ m1_subset_1(F_144,k1_zfmisc_1(k2_zfmisc_1(C_145,D_140)))
      | ~ v1_funct_1(F_144)
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_751,plain,(
    ! [A_143,B_141,E_142] :
      ( k1_partfun1(A_143,B_141,'#skF_2','#skF_1',E_142,'#skF_4') = k5_relat_1(E_142,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(resolution,[status(thm)],[c_84,c_743])).

tff(c_806,plain,(
    ! [A_151,B_152,E_153] :
      ( k1_partfun1(A_151,B_152,'#skF_2','#skF_1',E_153,'#skF_4') = k5_relat_1(E_153,'#skF_4')
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_1(E_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_751])).

tff(c_815,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_806])).

tff(c_825,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_815])).

tff(c_42,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_95,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42])).

tff(c_80,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_270,plain,(
    ! [D_82,C_83,A_84,B_85] :
      ( D_82 = C_83
      | ~ r2_relset_1(A_84,B_85,C_83,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_278,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_80,c_270])).

tff(c_293,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_278])).

tff(c_371,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_830,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_371])).

tff(c_1067,plain,(
    ! [F_163,C_162,E_165,D_160,A_161,B_164] :
      ( m1_subset_1(k1_partfun1(A_161,B_164,C_162,D_160,E_165,F_163),k1_zfmisc_1(k2_zfmisc_1(A_161,D_160)))
      | ~ m1_subset_1(F_163,k1_zfmisc_1(k2_zfmisc_1(C_162,D_160)))
      | ~ v1_funct_1(F_163)
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(A_161,B_164)))
      | ~ v1_funct_1(E_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1112,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_1067])).

tff(c_1140,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_88,c_84,c_1112])).

tff(c_1142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_830,c_1140])).

tff(c_1143,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_3743,plain,(
    ! [A_343,E_340,B_344,C_341,D_342] :
      ( k1_xboole_0 = C_341
      | v2_funct_1(E_340)
      | k2_relset_1(A_343,B_344,D_342) != B_344
      | ~ v2_funct_1(k1_partfun1(A_343,B_344,B_344,C_341,D_342,E_340))
      | ~ m1_subset_1(E_340,k1_zfmisc_1(k2_zfmisc_1(B_344,C_341)))
      | ~ v1_funct_2(E_340,B_344,C_341)
      | ~ v1_funct_1(E_340)
      | ~ m1_subset_1(D_342,k1_zfmisc_1(k2_zfmisc_1(A_343,B_344)))
      | ~ v1_funct_2(D_342,A_343,B_344)
      | ~ v1_funct_1(D_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_3750,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_3743])).

tff(c_3758,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_88,c_86,c_84,c_313,c_82,c_3750])).

tff(c_3760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_76,c_3758])).

tff(c_3761,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_3763,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3761])).

tff(c_200,plain,(
    ! [A_72,B_73,D_74] :
      ( r2_relset_1(A_72,B_73,D_74,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_207,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_95,c_200])).

tff(c_4136,plain,(
    ! [A_394,D_391,C_396,F_395,E_393,B_392] :
      ( k1_partfun1(A_394,B_392,C_396,D_391,E_393,F_395) = k5_relat_1(E_393,F_395)
      | ~ m1_subset_1(F_395,k1_zfmisc_1(k2_zfmisc_1(C_396,D_391)))
      | ~ v1_funct_1(F_395)
      | ~ m1_subset_1(E_393,k1_zfmisc_1(k2_zfmisc_1(A_394,B_392)))
      | ~ v1_funct_1(E_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4144,plain,(
    ! [A_394,B_392,E_393] :
      ( k1_partfun1(A_394,B_392,'#skF_2','#skF_1',E_393,'#skF_4') = k5_relat_1(E_393,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_393,k1_zfmisc_1(k2_zfmisc_1(A_394,B_392)))
      | ~ v1_funct_1(E_393) ) ),
    inference(resolution,[status(thm)],[c_84,c_4136])).

tff(c_4199,plain,(
    ! [A_402,B_403,E_404] :
      ( k1_partfun1(A_402,B_403,'#skF_2','#skF_1',E_404,'#skF_4') = k5_relat_1(E_404,'#skF_4')
      | ~ m1_subset_1(E_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(E_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_4144])).

tff(c_4208,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_4199])).

tff(c_4218,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_4208])).

tff(c_3764,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_4223,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4218,c_3764])).

tff(c_4461,plain,(
    ! [B_415,C_413,F_414,D_411,E_416,A_412] :
      ( m1_subset_1(k1_partfun1(A_412,B_415,C_413,D_411,E_416,F_414),k1_zfmisc_1(k2_zfmisc_1(A_412,D_411)))
      | ~ m1_subset_1(F_414,k1_zfmisc_1(k2_zfmisc_1(C_413,D_411)))
      | ~ v1_funct_1(F_414)
      | ~ m1_subset_1(E_416,k1_zfmisc_1(k2_zfmisc_1(A_412,B_415)))
      | ~ v1_funct_1(E_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4506,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4218,c_4461])).

tff(c_4534,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_88,c_84,c_4506])).

tff(c_4536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4223,c_4534])).

tff(c_4537,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_6126,plain,(
    ! [A_515,B_516,C_517,D_518] :
      ( k2_relset_1(A_515,B_516,C_517) = B_516
      | ~ r2_relset_1(B_516,B_516,k1_partfun1(B_516,A_515,A_515,B_516,D_518,C_517),k6_partfun1(B_516))
      | ~ m1_subset_1(D_518,k1_zfmisc_1(k2_zfmisc_1(B_516,A_515)))
      | ~ v1_funct_2(D_518,B_516,A_515)
      | ~ v1_funct_1(D_518)
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(A_515,B_516)))
      | ~ v1_funct_2(C_517,A_515,B_516)
      | ~ v1_funct_1(C_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_6132,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4537,c_6126])).

tff(c_6136,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_94,c_92,c_90,c_207,c_225,c_6132])).

tff(c_6138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3763,c_6136])).

tff(c_6140,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3761])).

tff(c_141,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_154,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_141])).

tff(c_3762,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_217,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_211])).

tff(c_224,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_217])).

tff(c_153,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_141])).

tff(c_32,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_relat_1(k2_relat_1(A_11)) != k5_relat_1(B_13,A_11)
      | k2_relat_1(B_13) != k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7727,plain,(
    ! [A_646,B_647] :
      ( k2_funct_1(A_646) = B_647
      | k6_partfun1(k2_relat_1(A_646)) != k5_relat_1(B_647,A_646)
      | k2_relat_1(B_647) != k1_relat_1(A_646)
      | ~ v2_funct_1(A_646)
      | ~ v1_funct_1(B_647)
      | ~ v1_relat_1(B_647)
      | ~ v1_funct_1(A_646)
      | ~ v1_relat_1(A_646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_32])).

tff(c_7729,plain,(
    ! [B_647] :
      ( k2_funct_1('#skF_4') = B_647
      | k5_relat_1(B_647,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_647) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_647)
      | ~ v1_relat_1(B_647)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6140,c_7727])).

tff(c_7816,plain,(
    ! [B_662] :
      ( k2_funct_1('#skF_4') = B_662
      | k5_relat_1(B_662,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_662) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_662)
      | ~ v1_relat_1(B_662) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_88,c_3762,c_7729])).

tff(c_7822,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_7816])).

tff(c_7834,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_224,c_7822])).

tff(c_7859,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7834])).

tff(c_6141,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6140,c_225])).

tff(c_8407,plain,(
    ! [A_718,C_719,B_720] :
      ( k6_partfun1(A_718) = k5_relat_1(C_719,k2_funct_1(C_719))
      | k1_xboole_0 = B_720
      | ~ v2_funct_1(C_719)
      | k2_relset_1(A_718,B_720,C_719) != B_720
      | ~ m1_subset_1(C_719,k1_zfmisc_1(k2_zfmisc_1(A_718,B_720)))
      | ~ v1_funct_2(C_719,A_718,B_720)
      | ~ v1_funct_1(C_719) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_8415,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_8407])).

tff(c_8426,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_6141,c_3762,c_8415])).

tff(c_8427,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_8426])).

tff(c_30,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_relat_1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_97,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_partfun1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30])).

tff(c_8451,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8427,c_97])).

tff(c_8460,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_88,c_3762,c_8451])).

tff(c_8511,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8460,c_103])).

tff(c_8539,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_8511])).

tff(c_8541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7859,c_8539])).

tff(c_8543,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7834])).

tff(c_8542,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7834])).

tff(c_8564,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8542])).

tff(c_6962,plain,(
    ! [A_600,B_598,E_599,D_597,F_601,C_602] :
      ( k1_partfun1(A_600,B_598,C_602,D_597,E_599,F_601) = k5_relat_1(E_599,F_601)
      | ~ m1_subset_1(F_601,k1_zfmisc_1(k2_zfmisc_1(C_602,D_597)))
      | ~ v1_funct_1(F_601)
      | ~ m1_subset_1(E_599,k1_zfmisc_1(k2_zfmisc_1(A_600,B_598)))
      | ~ v1_funct_1(E_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_6968,plain,(
    ! [A_600,B_598,E_599] :
      ( k1_partfun1(A_600,B_598,'#skF_2','#skF_1',E_599,'#skF_4') = k5_relat_1(E_599,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_599,k1_zfmisc_1(k2_zfmisc_1(A_600,B_598)))
      | ~ v1_funct_1(E_599) ) ),
    inference(resolution,[status(thm)],[c_84,c_6962])).

tff(c_7332,plain,(
    ! [A_621,B_622,E_623] :
      ( k1_partfun1(A_621,B_622,'#skF_2','#skF_1',E_623,'#skF_4') = k5_relat_1(E_623,'#skF_4')
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(A_621,B_622)))
      | ~ v1_funct_1(E_623) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_6968])).

tff(c_7341,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_7332])).

tff(c_7351,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_7341])).

tff(c_6155,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_7361,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7351,c_6155])).

tff(c_7547,plain,(
    ! [F_639,E_641,B_640,A_637,D_636,C_638] :
      ( m1_subset_1(k1_partfun1(A_637,B_640,C_638,D_636,E_641,F_639),k1_zfmisc_1(k2_zfmisc_1(A_637,D_636)))
      | ~ m1_subset_1(F_639,k1_zfmisc_1(k2_zfmisc_1(C_638,D_636)))
      | ~ v1_funct_1(F_639)
      | ~ m1_subset_1(E_641,k1_zfmisc_1(k2_zfmisc_1(A_637,B_640)))
      | ~ v1_funct_1(E_641) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_7596,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7351,c_7547])).

tff(c_7619,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_88,c_84,c_7596])).

tff(c_7621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7361,c_7619])).

tff(c_7622,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_8575,plain,(
    ! [F_725,E_723,C_726,B_722,A_724,D_721] :
      ( k1_partfun1(A_724,B_722,C_726,D_721,E_723,F_725) = k5_relat_1(E_723,F_725)
      | ~ m1_subset_1(F_725,k1_zfmisc_1(k2_zfmisc_1(C_726,D_721)))
      | ~ v1_funct_1(F_725)
      | ~ m1_subset_1(E_723,k1_zfmisc_1(k2_zfmisc_1(A_724,B_722)))
      | ~ v1_funct_1(E_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_8581,plain,(
    ! [A_724,B_722,E_723] :
      ( k1_partfun1(A_724,B_722,'#skF_2','#skF_1',E_723,'#skF_4') = k5_relat_1(E_723,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_723,k1_zfmisc_1(k2_zfmisc_1(A_724,B_722)))
      | ~ v1_funct_1(E_723) ) ),
    inference(resolution,[status(thm)],[c_84,c_8575])).

tff(c_8604,plain,(
    ! [A_727,B_728,E_729] :
      ( k1_partfun1(A_727,B_728,'#skF_2','#skF_1',E_729,'#skF_4') = k5_relat_1(E_729,'#skF_4')
      | ~ m1_subset_1(E_729,k1_zfmisc_1(k2_zfmisc_1(A_727,B_728)))
      | ~ v1_funct_1(E_729) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8581])).

tff(c_8610,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_8604])).

tff(c_8619,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_7622,c_8610])).

tff(c_8621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8564,c_8619])).

tff(c_8622,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8542])).

tff(c_8634,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8622,c_97])).

tff(c_8658,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_88,c_3762,c_8543,c_8634])).

tff(c_26,plain,(
    ! [A_9] :
      ( k1_relat_1(k2_funct_1(A_9)) = k2_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8640,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8622,c_26])).

tff(c_8662,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_88,c_3762,c_6140,c_8640])).

tff(c_78,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_7737,plain,(
    ! [B_647] :
      ( k2_funct_1('#skF_3') = B_647
      | k5_relat_1(B_647,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_647) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_647)
      | ~ v1_relat_1(B_647)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_7727])).

tff(c_7753,plain,(
    ! [B_647] :
      ( k2_funct_1('#skF_3') = B_647
      | k5_relat_1(B_647,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_647) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_647)
      | ~ v1_relat_1(B_647) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_94,c_78,c_7737])).

tff(c_8976,plain,(
    ! [B_757] :
      ( k2_funct_1('#skF_3') = B_757
      | k5_relat_1(B_757,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_757) != '#skF_1'
      | ~ v1_funct_1(B_757)
      | ~ v1_relat_1(B_757) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8662,c_7753])).

tff(c_8982,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_154,c_8976])).

tff(c_8998,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_6140,c_8658,c_8982])).

tff(c_9000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:43:04 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.95/2.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.95/2.78  
% 7.95/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.95/2.78  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.95/2.78  
% 7.95/2.78  %Foreground sorts:
% 7.95/2.78  
% 7.95/2.78  
% 7.95/2.78  %Background operators:
% 7.95/2.78  
% 7.95/2.78  
% 7.95/2.78  %Foreground operators:
% 7.95/2.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.95/2.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.95/2.78  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.95/2.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.95/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.95/2.78  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.95/2.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.95/2.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.95/2.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.95/2.78  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.95/2.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.95/2.78  tff('#skF_2', type, '#skF_2': $i).
% 7.95/2.78  tff('#skF_3', type, '#skF_3': $i).
% 7.95/2.78  tff('#skF_1', type, '#skF_1': $i).
% 7.95/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.95/2.78  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.95/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.95/2.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.95/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.95/2.78  tff('#skF_4', type, '#skF_4': $i).
% 7.95/2.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.95/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.95/2.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.95/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.95/2.78  
% 8.23/2.81  tff(f_250, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 8.23/2.81  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.23/2.81  tff(f_208, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.23/2.81  tff(f_149, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.23/2.81  tff(f_45, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 8.23/2.81  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.23/2.81  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 8.23/2.81  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 8.23/2.81  tff(f_147, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.23/2.81  tff(f_125, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 8.23/2.81  tff(f_123, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.23/2.81  tff(f_137, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.23/2.81  tff(f_192, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 8.23/2.81  tff(f_166, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 8.23/2.81  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.23/2.81  tff(f_107, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 8.23/2.81  tff(f_224, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 8.23/2.81  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 8.23/2.81  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 8.23/2.81  tff(c_72, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_250])).
% 8.23/2.81  tff(c_88, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_250])).
% 8.23/2.81  tff(c_86, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_250])).
% 8.23/2.81  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_250])).
% 8.23/2.81  tff(c_211, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.23/2.81  tff(c_225, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_211])).
% 8.23/2.81  tff(c_351, plain, (![C_91, A_92, B_93]: (v1_funct_1(k2_funct_1(C_91)) | k2_relset_1(A_92, B_93, C_91)!=B_93 | ~v2_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_2(C_91, A_92, B_93) | ~v1_funct_1(C_91))), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.23/2.81  tff(c_360, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_351])).
% 8.23/2.81  tff(c_369, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_225, c_360])).
% 8.23/2.81  tff(c_370, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_369])).
% 8.23/2.81  tff(c_76, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_250])).
% 8.23/2.81  tff(c_94, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_250])).
% 8.23/2.81  tff(c_92, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 8.23/2.81  tff(c_90, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_250])).
% 8.23/2.81  tff(c_50, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.23/2.81  tff(c_12, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.23/2.81  tff(c_101, plain, (![A_4]: (v1_relat_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_12])).
% 8.23/2.81  tff(c_14, plain, (![A_4]: (v1_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.23/2.81  tff(c_100, plain, (![A_4]: (v1_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 8.23/2.81  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.23/2.81  tff(c_104, plain, (![A_1]: (k1_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2])).
% 8.23/2.81  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.23/2.81  tff(c_103, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4])).
% 8.23/2.81  tff(c_6, plain, (![A_2]: (k5_relat_1(A_2, k6_relat_1(k2_relat_1(A_2)))=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.23/2.81  tff(c_155, plain, (![A_67]: (k5_relat_1(A_67, k6_partfun1(k2_relat_1(A_67)))=A_67 | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6])).
% 8.23/2.81  tff(c_164, plain, (![A_1]: (k5_relat_1(k6_partfun1(A_1), k6_partfun1(A_1))=k6_partfun1(A_1) | ~v1_relat_1(k6_partfun1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_155])).
% 8.23/2.81  tff(c_168, plain, (![A_1]: (k5_relat_1(k6_partfun1(A_1), k6_partfun1(A_1))=k6_partfun1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_164])).
% 8.23/2.81  tff(c_22, plain, (![A_6, B_8]: (v2_funct_1(A_6) | k6_relat_1(k1_relat_1(A_6))!=k5_relat_1(A_6, B_8) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.23/2.81  tff(c_294, plain, (![A_86, B_87]: (v2_funct_1(A_86) | k6_partfun1(k1_relat_1(A_86))!=k5_relat_1(A_86, B_87) | ~v1_funct_1(B_87) | ~v1_relat_1(B_87) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_22])).
% 8.23/2.81  tff(c_304, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)) | k6_partfun1(k1_relat_1(k6_partfun1(A_1)))!=k6_partfun1(A_1) | ~v1_funct_1(k6_partfun1(A_1)) | ~v1_relat_1(k6_partfun1(A_1)) | ~v1_funct_1(k6_partfun1(A_1)) | ~v1_relat_1(k6_partfun1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_168, c_294])).
% 8.23/2.81  tff(c_313, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_100, c_101, c_100, c_104, c_304])).
% 8.23/2.81  tff(c_82, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_250])).
% 8.23/2.81  tff(c_743, plain, (![A_143, C_145, E_142, B_141, F_144, D_140]: (k1_partfun1(A_143, B_141, C_145, D_140, E_142, F_144)=k5_relat_1(E_142, F_144) | ~m1_subset_1(F_144, k1_zfmisc_1(k2_zfmisc_1(C_145, D_140))) | ~v1_funct_1(F_144) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_141))) | ~v1_funct_1(E_142))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.23/2.81  tff(c_751, plain, (![A_143, B_141, E_142]: (k1_partfun1(A_143, B_141, '#skF_2', '#skF_1', E_142, '#skF_4')=k5_relat_1(E_142, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_141))) | ~v1_funct_1(E_142))), inference(resolution, [status(thm)], [c_84, c_743])).
% 8.23/2.81  tff(c_806, plain, (![A_151, B_152, E_153]: (k1_partfun1(A_151, B_152, '#skF_2', '#skF_1', E_153, '#skF_4')=k5_relat_1(E_153, '#skF_4') | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_1(E_153))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_751])).
% 8.23/2.81  tff(c_815, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_806])).
% 8.23/2.81  tff(c_825, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_815])).
% 8.23/2.81  tff(c_42, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.23/2.81  tff(c_95, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42])).
% 8.23/2.81  tff(c_80, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_250])).
% 8.23/2.81  tff(c_270, plain, (![D_82, C_83, A_84, B_85]: (D_82=C_83 | ~r2_relset_1(A_84, B_85, C_83, D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.23/2.81  tff(c_278, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_80, c_270])).
% 8.23/2.81  tff(c_293, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_278])).
% 8.23/2.81  tff(c_371, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_293])).
% 8.23/2.81  tff(c_830, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_825, c_371])).
% 8.23/2.81  tff(c_1067, plain, (![F_163, C_162, E_165, D_160, A_161, B_164]: (m1_subset_1(k1_partfun1(A_161, B_164, C_162, D_160, E_165, F_163), k1_zfmisc_1(k2_zfmisc_1(A_161, D_160))) | ~m1_subset_1(F_163, k1_zfmisc_1(k2_zfmisc_1(C_162, D_160))) | ~v1_funct_1(F_163) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(A_161, B_164))) | ~v1_funct_1(E_165))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.23/2.81  tff(c_1112, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_825, c_1067])).
% 8.23/2.81  tff(c_1140, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_88, c_84, c_1112])).
% 8.23/2.81  tff(c_1142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_830, c_1140])).
% 8.23/2.81  tff(c_1143, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_293])).
% 8.23/2.81  tff(c_3743, plain, (![A_343, E_340, B_344, C_341, D_342]: (k1_xboole_0=C_341 | v2_funct_1(E_340) | k2_relset_1(A_343, B_344, D_342)!=B_344 | ~v2_funct_1(k1_partfun1(A_343, B_344, B_344, C_341, D_342, E_340)) | ~m1_subset_1(E_340, k1_zfmisc_1(k2_zfmisc_1(B_344, C_341))) | ~v1_funct_2(E_340, B_344, C_341) | ~v1_funct_1(E_340) | ~m1_subset_1(D_342, k1_zfmisc_1(k2_zfmisc_1(A_343, B_344))) | ~v1_funct_2(D_342, A_343, B_344) | ~v1_funct_1(D_342))), inference(cnfTransformation, [status(thm)], [f_192])).
% 8.23/2.81  tff(c_3750, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1143, c_3743])).
% 8.23/2.81  tff(c_3758, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_90, c_88, c_86, c_84, c_313, c_82, c_3750])).
% 8.23/2.81  tff(c_3760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_76, c_3758])).
% 8.23/2.81  tff(c_3761, plain, (k2_relat_1('#skF_4')!='#skF_1' | v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_369])).
% 8.23/2.81  tff(c_3763, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_3761])).
% 8.23/2.81  tff(c_200, plain, (![A_72, B_73, D_74]: (r2_relset_1(A_72, B_73, D_74, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.23/2.81  tff(c_207, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_95, c_200])).
% 8.23/2.81  tff(c_4136, plain, (![A_394, D_391, C_396, F_395, E_393, B_392]: (k1_partfun1(A_394, B_392, C_396, D_391, E_393, F_395)=k5_relat_1(E_393, F_395) | ~m1_subset_1(F_395, k1_zfmisc_1(k2_zfmisc_1(C_396, D_391))) | ~v1_funct_1(F_395) | ~m1_subset_1(E_393, k1_zfmisc_1(k2_zfmisc_1(A_394, B_392))) | ~v1_funct_1(E_393))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.23/2.81  tff(c_4144, plain, (![A_394, B_392, E_393]: (k1_partfun1(A_394, B_392, '#skF_2', '#skF_1', E_393, '#skF_4')=k5_relat_1(E_393, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_393, k1_zfmisc_1(k2_zfmisc_1(A_394, B_392))) | ~v1_funct_1(E_393))), inference(resolution, [status(thm)], [c_84, c_4136])).
% 8.23/2.81  tff(c_4199, plain, (![A_402, B_403, E_404]: (k1_partfun1(A_402, B_403, '#skF_2', '#skF_1', E_404, '#skF_4')=k5_relat_1(E_404, '#skF_4') | ~m1_subset_1(E_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | ~v1_funct_1(E_404))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_4144])).
% 8.23/2.81  tff(c_4208, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_4199])).
% 8.23/2.81  tff(c_4218, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_4208])).
% 8.23/2.81  tff(c_3764, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_293])).
% 8.23/2.81  tff(c_4223, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4218, c_3764])).
% 8.23/2.81  tff(c_4461, plain, (![B_415, C_413, F_414, D_411, E_416, A_412]: (m1_subset_1(k1_partfun1(A_412, B_415, C_413, D_411, E_416, F_414), k1_zfmisc_1(k2_zfmisc_1(A_412, D_411))) | ~m1_subset_1(F_414, k1_zfmisc_1(k2_zfmisc_1(C_413, D_411))) | ~v1_funct_1(F_414) | ~m1_subset_1(E_416, k1_zfmisc_1(k2_zfmisc_1(A_412, B_415))) | ~v1_funct_1(E_416))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.23/2.81  tff(c_4506, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4218, c_4461])).
% 8.23/2.81  tff(c_4534, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_88, c_84, c_4506])).
% 8.23/2.81  tff(c_4536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4223, c_4534])).
% 8.23/2.81  tff(c_4537, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_293])).
% 8.23/2.81  tff(c_6126, plain, (![A_515, B_516, C_517, D_518]: (k2_relset_1(A_515, B_516, C_517)=B_516 | ~r2_relset_1(B_516, B_516, k1_partfun1(B_516, A_515, A_515, B_516, D_518, C_517), k6_partfun1(B_516)) | ~m1_subset_1(D_518, k1_zfmisc_1(k2_zfmisc_1(B_516, A_515))) | ~v1_funct_2(D_518, B_516, A_515) | ~v1_funct_1(D_518) | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(A_515, B_516))) | ~v1_funct_2(C_517, A_515, B_516) | ~v1_funct_1(C_517))), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.23/2.81  tff(c_6132, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4537, c_6126])).
% 8.23/2.81  tff(c_6136, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_94, c_92, c_90, c_207, c_225, c_6132])).
% 8.23/2.81  tff(c_6138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3763, c_6136])).
% 8.23/2.81  tff(c_6140, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_3761])).
% 8.23/2.81  tff(c_141, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.23/2.81  tff(c_154, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_141])).
% 8.23/2.81  tff(c_3762, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_369])).
% 8.23/2.81  tff(c_217, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_211])).
% 8.23/2.81  tff(c_224, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_217])).
% 8.23/2.81  tff(c_153, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_141])).
% 8.23/2.81  tff(c_32, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_relat_1(k2_relat_1(A_11))!=k5_relat_1(B_13, A_11) | k2_relat_1(B_13)!=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.23/2.81  tff(c_7727, plain, (![A_646, B_647]: (k2_funct_1(A_646)=B_647 | k6_partfun1(k2_relat_1(A_646))!=k5_relat_1(B_647, A_646) | k2_relat_1(B_647)!=k1_relat_1(A_646) | ~v2_funct_1(A_646) | ~v1_funct_1(B_647) | ~v1_relat_1(B_647) | ~v1_funct_1(A_646) | ~v1_relat_1(A_646))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_32])).
% 8.23/2.81  tff(c_7729, plain, (![B_647]: (k2_funct_1('#skF_4')=B_647 | k5_relat_1(B_647, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_647)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_647) | ~v1_relat_1(B_647) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6140, c_7727])).
% 8.23/2.81  tff(c_7816, plain, (![B_662]: (k2_funct_1('#skF_4')=B_662 | k5_relat_1(B_662, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_662)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_662) | ~v1_relat_1(B_662))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_88, c_3762, c_7729])).
% 8.23/2.81  tff(c_7822, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_153, c_7816])).
% 8.23/2.81  tff(c_7834, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_224, c_7822])).
% 8.23/2.81  tff(c_7859, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_7834])).
% 8.23/2.81  tff(c_6141, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6140, c_225])).
% 8.23/2.81  tff(c_8407, plain, (![A_718, C_719, B_720]: (k6_partfun1(A_718)=k5_relat_1(C_719, k2_funct_1(C_719)) | k1_xboole_0=B_720 | ~v2_funct_1(C_719) | k2_relset_1(A_718, B_720, C_719)!=B_720 | ~m1_subset_1(C_719, k1_zfmisc_1(k2_zfmisc_1(A_718, B_720))) | ~v1_funct_2(C_719, A_718, B_720) | ~v1_funct_1(C_719))), inference(cnfTransformation, [status(thm)], [f_224])).
% 8.23/2.81  tff(c_8415, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_8407])).
% 8.23/2.81  tff(c_8426, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_6141, c_3762, c_8415])).
% 8.23/2.81  tff(c_8427, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_76, c_8426])).
% 8.23/2.81  tff(c_30, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_relat_1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.23/2.81  tff(c_97, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_partfun1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_30])).
% 8.23/2.81  tff(c_8451, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8427, c_97])).
% 8.23/2.81  tff(c_8460, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_88, c_3762, c_8451])).
% 8.23/2.81  tff(c_8511, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8460, c_103])).
% 8.23/2.81  tff(c_8539, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_8511])).
% 8.23/2.81  tff(c_8541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7859, c_8539])).
% 8.23/2.81  tff(c_8543, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_7834])).
% 8.23/2.81  tff(c_8542, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_7834])).
% 8.23/2.81  tff(c_8564, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_8542])).
% 8.23/2.81  tff(c_6962, plain, (![A_600, B_598, E_599, D_597, F_601, C_602]: (k1_partfun1(A_600, B_598, C_602, D_597, E_599, F_601)=k5_relat_1(E_599, F_601) | ~m1_subset_1(F_601, k1_zfmisc_1(k2_zfmisc_1(C_602, D_597))) | ~v1_funct_1(F_601) | ~m1_subset_1(E_599, k1_zfmisc_1(k2_zfmisc_1(A_600, B_598))) | ~v1_funct_1(E_599))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.23/2.81  tff(c_6968, plain, (![A_600, B_598, E_599]: (k1_partfun1(A_600, B_598, '#skF_2', '#skF_1', E_599, '#skF_4')=k5_relat_1(E_599, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_599, k1_zfmisc_1(k2_zfmisc_1(A_600, B_598))) | ~v1_funct_1(E_599))), inference(resolution, [status(thm)], [c_84, c_6962])).
% 8.23/2.81  tff(c_7332, plain, (![A_621, B_622, E_623]: (k1_partfun1(A_621, B_622, '#skF_2', '#skF_1', E_623, '#skF_4')=k5_relat_1(E_623, '#skF_4') | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(A_621, B_622))) | ~v1_funct_1(E_623))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_6968])).
% 8.23/2.81  tff(c_7341, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_7332])).
% 8.23/2.81  tff(c_7351, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_7341])).
% 8.23/2.81  tff(c_6155, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_293])).
% 8.23/2.81  tff(c_7361, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_7351, c_6155])).
% 8.23/2.81  tff(c_7547, plain, (![F_639, E_641, B_640, A_637, D_636, C_638]: (m1_subset_1(k1_partfun1(A_637, B_640, C_638, D_636, E_641, F_639), k1_zfmisc_1(k2_zfmisc_1(A_637, D_636))) | ~m1_subset_1(F_639, k1_zfmisc_1(k2_zfmisc_1(C_638, D_636))) | ~v1_funct_1(F_639) | ~m1_subset_1(E_641, k1_zfmisc_1(k2_zfmisc_1(A_637, B_640))) | ~v1_funct_1(E_641))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.23/2.81  tff(c_7596, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7351, c_7547])).
% 8.23/2.81  tff(c_7619, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_88, c_84, c_7596])).
% 8.23/2.81  tff(c_7621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7361, c_7619])).
% 8.23/2.81  tff(c_7622, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_293])).
% 8.23/2.81  tff(c_8575, plain, (![F_725, E_723, C_726, B_722, A_724, D_721]: (k1_partfun1(A_724, B_722, C_726, D_721, E_723, F_725)=k5_relat_1(E_723, F_725) | ~m1_subset_1(F_725, k1_zfmisc_1(k2_zfmisc_1(C_726, D_721))) | ~v1_funct_1(F_725) | ~m1_subset_1(E_723, k1_zfmisc_1(k2_zfmisc_1(A_724, B_722))) | ~v1_funct_1(E_723))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.23/2.81  tff(c_8581, plain, (![A_724, B_722, E_723]: (k1_partfun1(A_724, B_722, '#skF_2', '#skF_1', E_723, '#skF_4')=k5_relat_1(E_723, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_723, k1_zfmisc_1(k2_zfmisc_1(A_724, B_722))) | ~v1_funct_1(E_723))), inference(resolution, [status(thm)], [c_84, c_8575])).
% 8.23/2.81  tff(c_8604, plain, (![A_727, B_728, E_729]: (k1_partfun1(A_727, B_728, '#skF_2', '#skF_1', E_729, '#skF_4')=k5_relat_1(E_729, '#skF_4') | ~m1_subset_1(E_729, k1_zfmisc_1(k2_zfmisc_1(A_727, B_728))) | ~v1_funct_1(E_729))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8581])).
% 8.23/2.81  tff(c_8610, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_8604])).
% 8.23/2.81  tff(c_8619, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_7622, c_8610])).
% 8.23/2.81  tff(c_8621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8564, c_8619])).
% 8.23/2.81  tff(c_8622, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_8542])).
% 8.23/2.81  tff(c_8634, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8622, c_97])).
% 8.23/2.81  tff(c_8658, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_88, c_3762, c_8543, c_8634])).
% 8.23/2.81  tff(c_26, plain, (![A_9]: (k1_relat_1(k2_funct_1(A_9))=k2_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.23/2.81  tff(c_8640, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8622, c_26])).
% 8.23/2.81  tff(c_8662, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_88, c_3762, c_6140, c_8640])).
% 8.23/2.81  tff(c_78, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_250])).
% 8.23/2.81  tff(c_7737, plain, (![B_647]: (k2_funct_1('#skF_3')=B_647 | k5_relat_1(B_647, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_647)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_647) | ~v1_relat_1(B_647) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_224, c_7727])).
% 8.23/2.81  tff(c_7753, plain, (![B_647]: (k2_funct_1('#skF_3')=B_647 | k5_relat_1(B_647, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_647)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_647) | ~v1_relat_1(B_647))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_94, c_78, c_7737])).
% 8.23/2.81  tff(c_8976, plain, (![B_757]: (k2_funct_1('#skF_3')=B_757 | k5_relat_1(B_757, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_757)!='#skF_1' | ~v1_funct_1(B_757) | ~v1_relat_1(B_757))), inference(demodulation, [status(thm), theory('equality')], [c_8662, c_7753])).
% 8.23/2.81  tff(c_8982, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_154, c_8976])).
% 8.23/2.81  tff(c_8998, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_6140, c_8658, c_8982])).
% 8.23/2.81  tff(c_9000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_8998])).
% 8.23/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/2.81  
% 8.23/2.81  Inference rules
% 8.23/2.81  ----------------------
% 8.23/2.81  #Ref     : 0
% 8.23/2.81  #Sup     : 1888
% 8.23/2.81  #Fact    : 0
% 8.23/2.81  #Define  : 0
% 8.23/2.81  #Split   : 53
% 8.23/2.81  #Chain   : 0
% 8.23/2.81  #Close   : 0
% 8.23/2.81  
% 8.23/2.81  Ordering : KBO
% 8.23/2.81  
% 8.23/2.81  Simplification rules
% 8.23/2.81  ----------------------
% 8.23/2.81  #Subsume      : 73
% 8.23/2.81  #Demod        : 3183
% 8.23/2.81  #Tautology    : 767
% 8.23/2.81  #SimpNegUnit  : 96
% 8.23/2.81  #BackRed      : 114
% 8.23/2.81  
% 8.23/2.81  #Partial instantiations: 0
% 8.23/2.81  #Strategies tried      : 1
% 8.23/2.81  
% 8.23/2.81  Timing (in seconds)
% 8.23/2.81  ----------------------
% 8.23/2.81  Preprocessing        : 0.40
% 8.23/2.81  Parsing              : 0.21
% 8.23/2.81  CNF conversion       : 0.03
% 8.23/2.81  Main loop            : 1.62
% 8.23/2.81  Inferencing          : 0.52
% 8.23/2.81  Reduction            : 0.66
% 8.23/2.81  Demodulation         : 0.50
% 8.23/2.81  BG Simplification    : 0.06
% 8.23/2.81  Subsumption          : 0.27
% 8.23/2.81  Abstraction          : 0.08
% 8.23/2.82  MUC search           : 0.00
% 8.23/2.82  Cooper               : 0.00
% 8.23/2.82  Total                : 2.08
% 8.23/2.82  Index Insertion      : 0.00
% 8.23/2.82  Index Deletion       : 0.00
% 8.23/2.82  Index Matching       : 0.00
% 8.23/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
