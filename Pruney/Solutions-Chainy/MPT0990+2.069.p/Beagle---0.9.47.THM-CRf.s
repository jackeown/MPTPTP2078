%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:05 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :  190 (1447 expanded)
%              Number of leaves         :   46 ( 532 expanded)
%              Depth                    :   25
%              Number of atoms          :  397 (5697 expanded)
%              Number of equality atoms :  151 (1842 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_204,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_119,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_178,axiom,(
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

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_136,axiom,(
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

tff(f_75,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_162,axiom,(
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

tff(c_58,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_145,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_157,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_145])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_156,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_145])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_176,plain,(
    ! [A_73] :
      ( k4_relat_1(A_73) = k2_funct_1(A_73)
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_182,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_176])).

tff(c_188,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_80,c_182])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_198,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_206,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_198])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_195,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_4])).

tff(c_204,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_195])).

tff(c_42,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_relat_1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_partfun1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_220,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_83])).

tff(c_224,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_220])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_245,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_251,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_245])).

tff(c_257,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_251])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_192,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_6])).

tff(c_202,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_192])).

tff(c_14,plain,(
    ! [A_13] :
      ( k7_relat_1(A_13,k1_relat_1(A_13)) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_211,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_14])).

tff(c_215,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_211])).

tff(c_259,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_215])).

tff(c_38,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_155,plain,(
    ! [A_33] : v1_relat_1(k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_82,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_partfun1(A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_291,plain,(
    ! [A_81,B_82,C_83] :
      ( k5_relat_1(k5_relat_1(A_81,B_82),C_83) = k5_relat_1(A_81,k5_relat_1(B_82,C_83))
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_316,plain,(
    ! [A_11,B_12,C_83] :
      ( k5_relat_1(k6_partfun1(A_11),k5_relat_1(B_12,C_83)) = k5_relat_1(k7_relat_1(B_12,A_11),C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(k6_partfun1(A_11))
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_291])).

tff(c_1714,plain,(
    ! [A_151,B_152,C_153] :
      ( k5_relat_1(k6_partfun1(A_151),k5_relat_1(B_152,C_153)) = k5_relat_1(k7_relat_1(B_152,A_151),C_153)
      | ~ v1_relat_1(C_153)
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_316])).

tff(c_1820,plain,(
    ! [A_10,A_151] :
      ( k5_relat_1(k7_relat_1(A_10,A_151),k6_partfun1(k2_relat_1(A_10))) = k5_relat_1(k6_partfun1(A_151),A_10)
      | ~ v1_relat_1(k6_partfun1(k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_1714])).

tff(c_2181,plain,(
    ! [A_174,A_175] :
      ( k5_relat_1(k7_relat_1(A_174,A_175),k6_partfun1(k2_relat_1(A_174))) = k5_relat_1(k6_partfun1(A_175),A_174)
      | ~ v1_relat_1(A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_1820])).

tff(c_2208,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_2181])).

tff(c_2234,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_224,c_204,c_2208])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_2333,plain,(
    ! [A_179,C_180,B_181] :
      ( k6_partfun1(A_179) = k5_relat_1(C_180,k2_funct_1(C_180))
      | k1_xboole_0 = B_181
      | ~ v2_funct_1(C_180)
      | k2_relset_1(A_179,B_181,C_180) != B_181
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_179,B_181)))
      | ~ v1_funct_2(C_180,A_179,B_181)
      | ~ v1_funct_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2337,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2333])).

tff(c_2345,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_68,c_64,c_2337])).

tff(c_2346,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2345])).

tff(c_4308,plain,(
    ! [B_269,C_270,A_271] :
      ( k6_partfun1(B_269) = k5_relat_1(k2_funct_1(C_270),C_270)
      | k1_xboole_0 = B_269
      | ~ v2_funct_1(C_270)
      | k2_relset_1(A_271,B_269,C_270) != B_269
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_271,B_269)))
      | ~ v1_funct_2(C_270,A_271,B_269)
      | ~ v1_funct_1(C_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_4312,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4308])).

tff(c_4320,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_68,c_64,c_4312])).

tff(c_4321,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4320])).

tff(c_8,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4332,plain,(
    ! [C_9] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_9)) = k5_relat_1(k6_partfun1('#skF_2'),C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4321,c_8])).

tff(c_5449,plain,(
    ! [C_312] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_312)) = k5_relat_1(k6_partfun1('#skF_2'),C_312)
      | ~ v1_relat_1(C_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_156,c_4332])).

tff(c_5467,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2346,c_5449])).

tff(c_5510,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_2234,c_5467])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1139,plain,(
    ! [E_121,B_122,F_120,D_119,A_118,C_123] :
      ( k1_partfun1(A_118,B_122,C_123,D_119,E_121,F_120) = k5_relat_1(E_121,F_120)
      | ~ m1_subset_1(F_120,k1_zfmisc_1(k2_zfmisc_1(C_123,D_119)))
      | ~ v1_funct_1(F_120)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_118,B_122)))
      | ~ v1_funct_1(E_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1145,plain,(
    ! [A_118,B_122,E_121] :
      ( k1_partfun1(A_118,B_122,'#skF_2','#skF_1',E_121,'#skF_4') = k5_relat_1(E_121,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_118,B_122)))
      | ~ v1_funct_1(E_121) ) ),
    inference(resolution,[status(thm)],[c_70,c_1139])).

tff(c_1575,plain,(
    ! [A_140,B_141,E_142] :
      ( k1_partfun1(A_140,B_141,'#skF_2','#skF_1',E_142,'#skF_4') = k5_relat_1(E_142,'#skF_4')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1145])).

tff(c_1581,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1575])).

tff(c_1588,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1581])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_695,plain,(
    ! [D_98,C_99,A_100,B_101] :
      ( D_98 = C_99
      | ~ r2_relset_1(A_100,B_101,C_99,D_98)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_703,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_695])).

tff(c_718,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_703])).

tff(c_803,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_718])).

tff(c_1593,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_803])).

tff(c_1609,plain,(
    ! [C_144,B_147,D_145,F_143,A_148,E_146] :
      ( m1_subset_1(k1_partfun1(A_148,B_147,C_144,D_145,E_146,F_143),k1_zfmisc_1(k2_zfmisc_1(A_148,D_145)))
      | ~ m1_subset_1(F_143,k1_zfmisc_1(k2_zfmisc_1(C_144,D_145)))
      | ~ v1_funct_1(F_143)
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147)))
      | ~ v1_funct_1(E_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1640,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1588,c_1609])).

tff(c_1654,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_1640])).

tff(c_1656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1593,c_1654])).

tff(c_1657,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_718])).

tff(c_2041,plain,(
    ! [C_171,A_166,E_169,F_168,D_167,B_170] :
      ( k1_partfun1(A_166,B_170,C_171,D_167,E_169,F_168) = k5_relat_1(E_169,F_168)
      | ~ m1_subset_1(F_168,k1_zfmisc_1(k2_zfmisc_1(C_171,D_167)))
      | ~ v1_funct_1(F_168)
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_166,B_170)))
      | ~ v1_funct_1(E_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2047,plain,(
    ! [A_166,B_170,E_169] :
      ( k1_partfun1(A_166,B_170,'#skF_2','#skF_1',E_169,'#skF_4') = k5_relat_1(E_169,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_166,B_170)))
      | ~ v1_funct_1(E_169) ) ),
    inference(resolution,[status(thm)],[c_70,c_2041])).

tff(c_4206,plain,(
    ! [A_266,B_267,E_268] :
      ( k1_partfun1(A_266,B_267,'#skF_2','#skF_1',E_268,'#skF_4') = k5_relat_1(E_268,'#skF_4')
      | ~ m1_subset_1(E_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267)))
      | ~ v1_funct_1(E_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2047])).

tff(c_4212,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4206])).

tff(c_4219,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1657,c_4212])).

tff(c_5464,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4219,c_5449])).

tff(c_5508,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_5464])).

tff(c_5537,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5510,c_5508])).

tff(c_5550,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k2_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5537,c_82])).

tff(c_5563,plain,(
    k7_relat_1('#skF_4','#skF_2') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_5550])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_258,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_245])).

tff(c_2339,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_2333])).

tff(c_2349,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_258,c_2339])).

tff(c_2350,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2349])).

tff(c_2399,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2350])).

tff(c_234,plain,(
    ! [A_74,B_75,D_76] :
      ( r2_relset_1(A_74,B_75,D_76,D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_241,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_38,c_234])).

tff(c_3187,plain,(
    ! [A_217,B_218,C_219,D_220] :
      ( k2_relset_1(A_217,B_218,C_219) = B_218
      | ~ r2_relset_1(B_218,B_218,k1_partfun1(B_218,A_217,A_217,B_218,D_220,C_219),k6_partfun1(B_218))
      | ~ m1_subset_1(D_220,k1_zfmisc_1(k2_zfmisc_1(B_218,A_217)))
      | ~ v1_funct_2(D_220,B_218,A_217)
      | ~ v1_funct_1(D_220)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ v1_funct_2(C_219,A_217,B_218)
      | ~ v1_funct_1(C_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3193,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_3187])).

tff(c_3197,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_76,c_241,c_258,c_3193])).

tff(c_3199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2399,c_3197])).

tff(c_3200,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2350])).

tff(c_3250,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3200])).

tff(c_22,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22])).

tff(c_4157,plain,(
    ! [B_262,C_264,A_265,E_261,D_263] :
      ( k1_xboole_0 = C_264
      | v2_funct_1(E_261)
      | k2_relset_1(A_265,B_262,D_263) != B_262
      | ~ v2_funct_1(k1_partfun1(A_265,B_262,B_262,C_264,D_263,E_261))
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(B_262,C_264)))
      | ~ v1_funct_2(E_261,B_262,C_264)
      | ~ v1_funct_1(E_261)
      | ~ m1_subset_1(D_263,k1_zfmisc_1(k2_zfmisc_1(A_265,B_262)))
      | ~ v1_funct_2(D_263,A_265,B_262)
      | ~ v1_funct_1(D_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4161,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_4157])).

tff(c_4166,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_81,c_68,c_4161])).

tff(c_4168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3250,c_62,c_4166])).

tff(c_4170,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3200])).

tff(c_16,plain,(
    ! [A_14] :
      ( k4_relat_1(A_14) = k2_funct_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4173,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4170,c_16])).

tff(c_4176,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_74,c_4173])).

tff(c_4192,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4176,c_2])).

tff(c_4204,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_4192])).

tff(c_3201,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2350])).

tff(c_4186,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4176,c_6])).

tff(c_4200,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_3201,c_4186])).

tff(c_4229,plain,
    ( k7_relat_1(k2_funct_1('#skF_4'),'#skF_1') = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4200,c_14])).

tff(c_4235,plain,(
    k7_relat_1(k2_funct_1('#skF_4'),'#skF_1') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_4229])).

tff(c_264,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_83])).

tff(c_268,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_264])).

tff(c_260,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_202])).

tff(c_333,plain,(
    ! [A_11,B_12,C_83] :
      ( k5_relat_1(k6_partfun1(A_11),k5_relat_1(B_12,C_83)) = k5_relat_1(k7_relat_1(B_12,A_11),C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_316])).

tff(c_4329,plain,(
    ! [A_11] :
      ( k5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),A_11),'#skF_3') = k5_relat_1(k6_partfun1(A_11),k6_partfun1('#skF_2'))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4321,c_333])).

tff(c_5026,plain,(
    ! [A_306] : k5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),A_306),'#skF_3') = k5_relat_1(k6_partfun1(A_306),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_156,c_4329])).

tff(c_5045,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))),k6_partfun1('#skF_2')) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_5026])).

tff(c_5054,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_4321,c_260,c_5045])).

tff(c_4169,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3200])).

tff(c_4288,plain,(
    ! [A_11] :
      ( k5_relat_1(k7_relat_1('#skF_4',A_11),k2_funct_1('#skF_4')) = k5_relat_1(k6_partfun1(A_11),k6_partfun1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4169,c_333])).

tff(c_5586,plain,(
    ! [A_313] : k5_relat_1(k7_relat_1('#skF_4',A_313),k2_funct_1('#skF_4')) = k5_relat_1(k6_partfun1(A_313),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_4204,c_4288])).

tff(c_5601,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) = k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5563,c_5586])).

tff(c_5615,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5054,c_5601])).

tff(c_2360,plain,(
    ! [C_9] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_9)) = k5_relat_1(k6_partfun1('#skF_1'),C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2346,c_8])).

tff(c_6666,plain,(
    ! [C_326] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_326)) = k5_relat_1(k6_partfun1('#skF_1'),C_326)
      | ~ v1_relat_1(C_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_206,c_2360])).

tff(c_6714,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k5_relat_1('#skF_3',k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5615,c_6666])).

tff(c_6769,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_268,c_6714])).

tff(c_6902,plain,
    ( k7_relat_1(k2_funct_1('#skF_4'),'#skF_1') = '#skF_3'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6769,c_82])).

tff(c_6922,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_4235,c_6902])).

tff(c_4189,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4176,c_4])).

tff(c_4202,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_4189])).

tff(c_6937,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6922,c_4202])).

tff(c_6946,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_6937])).

tff(c_7052,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6946,c_14])).

tff(c_7058,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_5563,c_7052])).

tff(c_7060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:36:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.23/2.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/2.60  
% 7.23/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.43/2.60  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.43/2.60  
% 7.43/2.60  %Foreground sorts:
% 7.43/2.60  
% 7.43/2.60  
% 7.43/2.60  %Background operators:
% 7.43/2.60  
% 7.43/2.60  
% 7.43/2.60  %Foreground operators:
% 7.43/2.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.43/2.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.43/2.60  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.43/2.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.43/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.43/2.60  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.43/2.60  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.43/2.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.43/2.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.43/2.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.43/2.60  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.43/2.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.43/2.60  tff('#skF_2', type, '#skF_2': $i).
% 7.43/2.60  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.43/2.60  tff('#skF_3', type, '#skF_3': $i).
% 7.43/2.60  tff('#skF_1', type, '#skF_1': $i).
% 7.43/2.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.43/2.60  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.43/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.43/2.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.43/2.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.43/2.60  tff('#skF_4', type, '#skF_4': $i).
% 7.43/2.60  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.43/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.43/2.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.43/2.60  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.43/2.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.43/2.60  
% 7.43/2.63  tff(f_204, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.43/2.63  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.43/2.63  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 7.43/2.63  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 7.43/2.63  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 7.43/2.63  tff(f_119, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.43/2.63  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 7.43/2.63  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.43/2.63  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 7.43/2.63  tff(f_107, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.43/2.63  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 7.43/2.63  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 7.43/2.63  tff(f_178, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 7.43/2.63  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.43/2.63  tff(f_91, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.43/2.63  tff(f_103, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.43/2.63  tff(f_136, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.43/2.63  tff(f_75, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 7.43/2.63  tff(f_162, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 7.43/2.63  tff(c_58, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_145, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.43/2.63  tff(c_157, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_145])).
% 7.43/2.63  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_156, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_145])).
% 7.43/2.63  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_176, plain, (![A_73]: (k4_relat_1(A_73)=k2_funct_1(A_73) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.43/2.63  tff(c_182, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_176])).
% 7.43/2.63  tff(c_188, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_80, c_182])).
% 7.43/2.63  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.43/2.63  tff(c_198, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_188, c_2])).
% 7.43/2.63  tff(c_206, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_198])).
% 7.43/2.63  tff(c_4, plain, (![A_2]: (k2_relat_1(k4_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.43/2.63  tff(c_195, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_188, c_4])).
% 7.43/2.63  tff(c_204, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_195])).
% 7.43/2.63  tff(c_42, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.43/2.63  tff(c_10, plain, (![A_10]: (k5_relat_1(A_10, k6_relat_1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.43/2.63  tff(c_83, plain, (![A_10]: (k5_relat_1(A_10, k6_partfun1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 7.43/2.63  tff(c_220, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_83])).
% 7.43/2.63  tff(c_224, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_220])).
% 7.43/2.63  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_245, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.43/2.63  tff(c_251, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_245])).
% 7.43/2.63  tff(c_257, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_251])).
% 7.43/2.63  tff(c_6, plain, (![A_2]: (k1_relat_1(k4_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.43/2.63  tff(c_192, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_188, c_6])).
% 7.43/2.63  tff(c_202, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_192])).
% 7.43/2.63  tff(c_14, plain, (![A_13]: (k7_relat_1(A_13, k1_relat_1(A_13))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.43/2.63  tff(c_211, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_14])).
% 7.43/2.63  tff(c_215, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_211])).
% 7.43/2.63  tff(c_259, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_215])).
% 7.43/2.63  tff(c_38, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.43/2.63  tff(c_155, plain, (![A_33]: (v1_relat_1(k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_38, c_145])).
% 7.43/2.63  tff(c_12, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.43/2.63  tff(c_82, plain, (![A_11, B_12]: (k5_relat_1(k6_partfun1(A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_12])).
% 7.43/2.63  tff(c_291, plain, (![A_81, B_82, C_83]: (k5_relat_1(k5_relat_1(A_81, B_82), C_83)=k5_relat_1(A_81, k5_relat_1(B_82, C_83)) | ~v1_relat_1(C_83) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.43/2.63  tff(c_316, plain, (![A_11, B_12, C_83]: (k5_relat_1(k6_partfun1(A_11), k5_relat_1(B_12, C_83))=k5_relat_1(k7_relat_1(B_12, A_11), C_83) | ~v1_relat_1(C_83) | ~v1_relat_1(B_12) | ~v1_relat_1(k6_partfun1(A_11)) | ~v1_relat_1(B_12))), inference(superposition, [status(thm), theory('equality')], [c_82, c_291])).
% 7.43/2.63  tff(c_1714, plain, (![A_151, B_152, C_153]: (k5_relat_1(k6_partfun1(A_151), k5_relat_1(B_152, C_153))=k5_relat_1(k7_relat_1(B_152, A_151), C_153) | ~v1_relat_1(C_153) | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_316])).
% 7.43/2.63  tff(c_1820, plain, (![A_10, A_151]: (k5_relat_1(k7_relat_1(A_10, A_151), k6_partfun1(k2_relat_1(A_10)))=k5_relat_1(k6_partfun1(A_151), A_10) | ~v1_relat_1(k6_partfun1(k2_relat_1(A_10))) | ~v1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_83, c_1714])).
% 7.43/2.63  tff(c_2181, plain, (![A_174, A_175]: (k5_relat_1(k7_relat_1(A_174, A_175), k6_partfun1(k2_relat_1(A_174)))=k5_relat_1(k6_partfun1(A_175), A_174) | ~v1_relat_1(A_174))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_1820])).
% 7.43/2.63  tff(c_2208, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_259, c_2181])).
% 7.43/2.63  tff(c_2234, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_224, c_204, c_2208])).
% 7.43/2.63  tff(c_60, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_2333, plain, (![A_179, C_180, B_181]: (k6_partfun1(A_179)=k5_relat_1(C_180, k2_funct_1(C_180)) | k1_xboole_0=B_181 | ~v2_funct_1(C_180) | k2_relset_1(A_179, B_181, C_180)!=B_181 | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_179, B_181))) | ~v1_funct_2(C_180, A_179, B_181) | ~v1_funct_1(C_180))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.43/2.63  tff(c_2337, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_2333])).
% 7.43/2.63  tff(c_2345, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_68, c_64, c_2337])).
% 7.43/2.63  tff(c_2346, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_2345])).
% 7.43/2.63  tff(c_4308, plain, (![B_269, C_270, A_271]: (k6_partfun1(B_269)=k5_relat_1(k2_funct_1(C_270), C_270) | k1_xboole_0=B_269 | ~v2_funct_1(C_270) | k2_relset_1(A_271, B_269, C_270)!=B_269 | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_271, B_269))) | ~v1_funct_2(C_270, A_271, B_269) | ~v1_funct_1(C_270))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.43/2.63  tff(c_4312, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_4308])).
% 7.43/2.63  tff(c_4320, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_68, c_64, c_4312])).
% 7.43/2.63  tff(c_4321, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_4320])).
% 7.43/2.63  tff(c_8, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.43/2.63  tff(c_4332, plain, (![C_9]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_9))=k5_relat_1(k6_partfun1('#skF_2'), C_9) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4321, c_8])).
% 7.43/2.63  tff(c_5449, plain, (![C_312]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_312))=k5_relat_1(k6_partfun1('#skF_2'), C_312) | ~v1_relat_1(C_312))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_156, c_4332])).
% 7.43/2.63  tff(c_5467, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2346, c_5449])).
% 7.43/2.63  tff(c_5510, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_2234, c_5467])).
% 7.43/2.63  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_1139, plain, (![E_121, B_122, F_120, D_119, A_118, C_123]: (k1_partfun1(A_118, B_122, C_123, D_119, E_121, F_120)=k5_relat_1(E_121, F_120) | ~m1_subset_1(F_120, k1_zfmisc_1(k2_zfmisc_1(C_123, D_119))) | ~v1_funct_1(F_120) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_118, B_122))) | ~v1_funct_1(E_121))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.43/2.63  tff(c_1145, plain, (![A_118, B_122, E_121]: (k1_partfun1(A_118, B_122, '#skF_2', '#skF_1', E_121, '#skF_4')=k5_relat_1(E_121, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_118, B_122))) | ~v1_funct_1(E_121))), inference(resolution, [status(thm)], [c_70, c_1139])).
% 7.43/2.63  tff(c_1575, plain, (![A_140, B_141, E_142]: (k1_partfun1(A_140, B_141, '#skF_2', '#skF_1', E_142, '#skF_4')=k5_relat_1(E_142, '#skF_4') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_1(E_142))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1145])).
% 7.43/2.63  tff(c_1581, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1575])).
% 7.43/2.63  tff(c_1588, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1581])).
% 7.43/2.63  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_695, plain, (![D_98, C_99, A_100, B_101]: (D_98=C_99 | ~r2_relset_1(A_100, B_101, C_99, D_98) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.43/2.63  tff(c_703, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_695])).
% 7.43/2.63  tff(c_718, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_703])).
% 7.43/2.63  tff(c_803, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_718])).
% 7.43/2.63  tff(c_1593, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_803])).
% 7.43/2.63  tff(c_1609, plain, (![C_144, B_147, D_145, F_143, A_148, E_146]: (m1_subset_1(k1_partfun1(A_148, B_147, C_144, D_145, E_146, F_143), k1_zfmisc_1(k2_zfmisc_1(A_148, D_145))) | ~m1_subset_1(F_143, k1_zfmisc_1(k2_zfmisc_1(C_144, D_145))) | ~v1_funct_1(F_143) | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))) | ~v1_funct_1(E_146))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.43/2.63  tff(c_1640, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1588, c_1609])).
% 7.43/2.63  tff(c_1654, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_1640])).
% 7.43/2.63  tff(c_1656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1593, c_1654])).
% 7.43/2.63  tff(c_1657, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_718])).
% 7.43/2.63  tff(c_2041, plain, (![C_171, A_166, E_169, F_168, D_167, B_170]: (k1_partfun1(A_166, B_170, C_171, D_167, E_169, F_168)=k5_relat_1(E_169, F_168) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(C_171, D_167))) | ~v1_funct_1(F_168) | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(A_166, B_170))) | ~v1_funct_1(E_169))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.43/2.63  tff(c_2047, plain, (![A_166, B_170, E_169]: (k1_partfun1(A_166, B_170, '#skF_2', '#skF_1', E_169, '#skF_4')=k5_relat_1(E_169, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(A_166, B_170))) | ~v1_funct_1(E_169))), inference(resolution, [status(thm)], [c_70, c_2041])).
% 7.43/2.63  tff(c_4206, plain, (![A_266, B_267, E_268]: (k1_partfun1(A_266, B_267, '#skF_2', '#skF_1', E_268, '#skF_4')=k5_relat_1(E_268, '#skF_4') | ~m1_subset_1(E_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))) | ~v1_funct_1(E_268))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2047])).
% 7.43/2.63  tff(c_4212, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_4206])).
% 7.43/2.63  tff(c_4219, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1657, c_4212])).
% 7.43/2.63  tff(c_5464, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4219, c_5449])).
% 7.43/2.63  tff(c_5508, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_5464])).
% 7.43/2.63  tff(c_5537, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5510, c_5508])).
% 7.43/2.63  tff(c_5550, plain, (k7_relat_1('#skF_4', '#skF_2')=k2_funct_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5537, c_82])).
% 7.43/2.63  tff(c_5563, plain, (k7_relat_1('#skF_4', '#skF_2')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_5550])).
% 7.43/2.63  tff(c_62, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.43/2.63  tff(c_258, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_245])).
% 7.43/2.63  tff(c_2339, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_2333])).
% 7.43/2.63  tff(c_2349, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_258, c_2339])).
% 7.43/2.63  tff(c_2350, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_2349])).
% 7.43/2.63  tff(c_2399, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2350])).
% 7.43/2.63  tff(c_234, plain, (![A_74, B_75, D_76]: (r2_relset_1(A_74, B_75, D_76, D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.43/2.63  tff(c_241, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_38, c_234])).
% 7.43/2.63  tff(c_3187, plain, (![A_217, B_218, C_219, D_220]: (k2_relset_1(A_217, B_218, C_219)=B_218 | ~r2_relset_1(B_218, B_218, k1_partfun1(B_218, A_217, A_217, B_218, D_220, C_219), k6_partfun1(B_218)) | ~m1_subset_1(D_220, k1_zfmisc_1(k2_zfmisc_1(B_218, A_217))) | ~v1_funct_2(D_220, B_218, A_217) | ~v1_funct_1(D_220) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~v1_funct_2(C_219, A_217, B_218) | ~v1_funct_1(C_219))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.43/2.63  tff(c_3193, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1657, c_3187])).
% 7.43/2.63  tff(c_3197, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_76, c_241, c_258, c_3193])).
% 7.43/2.63  tff(c_3199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2399, c_3197])).
% 7.43/2.63  tff(c_3200, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2350])).
% 7.43/2.63  tff(c_3250, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3200])).
% 7.43/2.63  tff(c_22, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.43/2.63  tff(c_81, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22])).
% 7.43/2.63  tff(c_4157, plain, (![B_262, C_264, A_265, E_261, D_263]: (k1_xboole_0=C_264 | v2_funct_1(E_261) | k2_relset_1(A_265, B_262, D_263)!=B_262 | ~v2_funct_1(k1_partfun1(A_265, B_262, B_262, C_264, D_263, E_261)) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(B_262, C_264))) | ~v1_funct_2(E_261, B_262, C_264) | ~v1_funct_1(E_261) | ~m1_subset_1(D_263, k1_zfmisc_1(k2_zfmisc_1(A_265, B_262))) | ~v1_funct_2(D_263, A_265, B_262) | ~v1_funct_1(D_263))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.43/2.63  tff(c_4161, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1657, c_4157])).
% 7.43/2.63  tff(c_4166, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_81, c_68, c_4161])).
% 7.43/2.63  tff(c_4168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3250, c_62, c_4166])).
% 7.43/2.63  tff(c_4170, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3200])).
% 7.43/2.63  tff(c_16, plain, (![A_14]: (k4_relat_1(A_14)=k2_funct_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.43/2.63  tff(c_4173, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4170, c_16])).
% 7.43/2.63  tff(c_4176, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_74, c_4173])).
% 7.43/2.63  tff(c_4192, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4176, c_2])).
% 7.43/2.63  tff(c_4204, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_4192])).
% 7.43/2.63  tff(c_3201, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2350])).
% 7.43/2.63  tff(c_4186, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4176, c_6])).
% 7.43/2.63  tff(c_4200, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_3201, c_4186])).
% 7.43/2.63  tff(c_4229, plain, (k7_relat_1(k2_funct_1('#skF_4'), '#skF_1')=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4200, c_14])).
% 7.43/2.63  tff(c_4235, plain, (k7_relat_1(k2_funct_1('#skF_4'), '#skF_1')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_4229])).
% 7.43/2.63  tff(c_264, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_257, c_83])).
% 7.43/2.63  tff(c_268, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_264])).
% 7.43/2.63  tff(c_260, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_257, c_202])).
% 7.43/2.63  tff(c_333, plain, (![A_11, B_12, C_83]: (k5_relat_1(k6_partfun1(A_11), k5_relat_1(B_12, C_83))=k5_relat_1(k7_relat_1(B_12, A_11), C_83) | ~v1_relat_1(C_83) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_316])).
% 7.43/2.63  tff(c_4329, plain, (![A_11]: (k5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), A_11), '#skF_3')=k5_relat_1(k6_partfun1(A_11), k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4321, c_333])).
% 7.43/2.63  tff(c_5026, plain, (![A_306]: (k5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), A_306), '#skF_3')=k5_relat_1(k6_partfun1(A_306), k6_partfun1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_156, c_4329])).
% 7.43/2.63  tff(c_5045, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))), k6_partfun1('#skF_2'))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_5026])).
% 7.43/2.63  tff(c_5054, plain, (k5_relat_1(k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_4321, c_260, c_5045])).
% 7.43/2.63  tff(c_4169, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3200])).
% 7.43/2.63  tff(c_4288, plain, (![A_11]: (k5_relat_1(k7_relat_1('#skF_4', A_11), k2_funct_1('#skF_4'))=k5_relat_1(k6_partfun1(A_11), k6_partfun1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4169, c_333])).
% 7.43/2.63  tff(c_5586, plain, (![A_313]: (k5_relat_1(k7_relat_1('#skF_4', A_313), k2_funct_1('#skF_4'))=k5_relat_1(k6_partfun1(A_313), k6_partfun1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_4204, c_4288])).
% 7.43/2.63  tff(c_5601, plain, (k5_relat_1(k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))=k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5563, c_5586])).
% 7.43/2.63  tff(c_5615, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5054, c_5601])).
% 7.43/2.63  tff(c_2360, plain, (![C_9]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_9))=k5_relat_1(k6_partfun1('#skF_1'), C_9) | ~v1_relat_1(C_9) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2346, c_8])).
% 7.43/2.63  tff(c_6666, plain, (![C_326]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_326))=k5_relat_1(k6_partfun1('#skF_1'), C_326) | ~v1_relat_1(C_326))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_206, c_2360])).
% 7.43/2.63  tff(c_6714, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k5_relat_1('#skF_3', k6_partfun1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5615, c_6666])).
% 7.43/2.63  tff(c_6769, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_268, c_6714])).
% 7.43/2.63  tff(c_6902, plain, (k7_relat_1(k2_funct_1('#skF_4'), '#skF_1')='#skF_3' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6769, c_82])).
% 7.43/2.63  tff(c_6922, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_4235, c_6902])).
% 7.43/2.63  tff(c_4189, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4176, c_4])).
% 7.43/2.63  tff(c_4202, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_4189])).
% 7.43/2.63  tff(c_6937, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6922, c_4202])).
% 7.43/2.63  tff(c_6946, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_257, c_6937])).
% 7.43/2.63  tff(c_7052, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6946, c_14])).
% 7.43/2.63  tff(c_7058, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_5563, c_7052])).
% 7.43/2.63  tff(c_7060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_7058])).
% 7.43/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.43/2.63  
% 7.43/2.63  Inference rules
% 7.43/2.63  ----------------------
% 7.43/2.63  #Ref     : 0
% 7.43/2.63  #Sup     : 1542
% 7.43/2.63  #Fact    : 0
% 7.43/2.63  #Define  : 0
% 7.43/2.63  #Split   : 14
% 7.43/2.63  #Chain   : 0
% 7.43/2.63  #Close   : 0
% 7.43/2.63  
% 7.43/2.63  Ordering : KBO
% 7.43/2.63  
% 7.43/2.63  Simplification rules
% 7.43/2.63  ----------------------
% 7.43/2.63  #Subsume      : 20
% 7.43/2.63  #Demod        : 2301
% 7.43/2.63  #Tautology    : 717
% 7.43/2.63  #SimpNegUnit  : 47
% 7.43/2.63  #BackRed      : 63
% 7.43/2.63  
% 7.43/2.63  #Partial instantiations: 0
% 7.43/2.63  #Strategies tried      : 1
% 7.43/2.63  
% 7.43/2.63  Timing (in seconds)
% 7.43/2.63  ----------------------
% 7.43/2.63  Preprocessing        : 0.38
% 7.43/2.63  Parsing              : 0.20
% 7.43/2.63  CNF conversion       : 0.03
% 7.43/2.63  Main loop            : 1.48
% 7.43/2.63  Inferencing          : 0.46
% 7.43/2.63  Reduction            : 0.65
% 7.43/2.63  Demodulation         : 0.51
% 7.43/2.63  BG Simplification    : 0.05
% 7.43/2.63  Subsumption          : 0.22
% 7.43/2.63  Abstraction          : 0.07
% 7.43/2.63  MUC search           : 0.00
% 7.43/2.63  Cooper               : 0.00
% 7.43/2.63  Total                : 1.91
% 7.43/2.63  Index Insertion      : 0.00
% 7.43/2.63  Index Deletion       : 0.00
% 7.43/2.63  Index Matching       : 0.00
% 7.43/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
