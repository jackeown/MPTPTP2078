%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:21 EST 2020

% Result     : Theorem 11.47s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 669 expanded)
%              Number of leaves         :   38 ( 273 expanded)
%              Depth                    :   12
%              Number of atoms          :  439 (3516 expanded)
%              Number of equality atoms :  151 (1133 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_173,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_115,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_131,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_73,axiom,(
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

tff(f_147,axiom,(
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

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_124,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_131,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_124])).

tff(c_145,plain,(
    ! [B_60,A_61,C_62] :
      ( k1_xboole_0 = B_60
      | k1_relset_1(A_61,B_60,C_62) = A_61
      | ~ v1_funct_2(C_62,A_61,B_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_148,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_145])).

tff(c_154,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_131,c_148])).

tff(c_155,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_154])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_86])).

tff(c_95,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_89])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_92,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_86])).

tff(c_98,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_132,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_124])).

tff(c_151,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_145])).

tff(c_158,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_132,c_151])).

tff(c_159,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_158])).

tff(c_36,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_relat_1(k1_relat_1(A_7)) != k5_relat_1(A_7,B_9)
      | k2_relat_1(A_7) != k1_relat_1(B_9)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_654,plain,(
    ! [A_132,B_133] :
      ( k2_funct_1(A_132) = B_133
      | k6_partfun1(k1_relat_1(A_132)) != k5_relat_1(A_132,B_133)
      | k2_relat_1(A_132) != k1_relat_1(B_133)
      | ~ v2_funct_1(A_132)
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_656,plain,(
    ! [B_133] :
      ( k2_funct_1('#skF_3') = B_133
      | k5_relat_1('#skF_3',B_133) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_133)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_654])).

tff(c_10815,plain,(
    ! [B_474] :
      ( k2_funct_1('#skF_3') = B_474
      | k5_relat_1('#skF_3',B_474) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_474)
      | ~ v1_funct_1(B_474)
      | ~ v1_relat_1(B_474) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_70,c_54,c_656])).

tff(c_10824,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_95,c_10815])).

tff(c_10834,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_155,c_10824])).

tff(c_10835,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_10834])).

tff(c_10837,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_10835])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_10775,plain,(
    ! [C_471,B_472,A_473] :
      ( v1_funct_2(k2_funct_1(C_471),B_472,A_473)
      | k2_relset_1(A_473,B_472,C_471) != B_472
      | ~ v2_funct_1(C_471)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(A_473,B_472)))
      | ~ v1_funct_2(C_471,A_473,B_472)
      | ~ v1_funct_1(C_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10787,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_10775])).

tff(c_10795,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_10787])).

tff(c_10942,plain,(
    ! [C_496,B_497,A_498] :
      ( m1_subset_1(k2_funct_1(C_496),k1_zfmisc_1(k2_zfmisc_1(B_497,A_498)))
      | k2_relset_1(A_498,B_497,C_496) != B_497
      | ~ v2_funct_1(C_496)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(k2_zfmisc_1(A_498,B_497)))
      | ~ v1_funct_2(C_496,A_498,B_497)
      | ~ v1_funct_1(C_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12228,plain,(
    ! [B_535,A_536,C_537] :
      ( k1_relset_1(B_535,A_536,k2_funct_1(C_537)) = k1_relat_1(k2_funct_1(C_537))
      | k2_relset_1(A_536,B_535,C_537) != B_535
      | ~ v2_funct_1(C_537)
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1(A_536,B_535)))
      | ~ v1_funct_2(C_537,A_536,B_535)
      | ~ v1_funct_1(C_537) ) ),
    inference(resolution,[status(thm)],[c_10942,c_12])).

tff(c_12264,plain,
    ( k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_12228])).

tff(c_12296,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_12264])).

tff(c_28,plain,(
    ! [B_18,A_17,C_19] :
      ( k1_xboole_0 = B_18
      | k1_relset_1(A_17,B_18,C_19) = A_17
      | ~ v1_funct_2(C_19,A_17,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12490,plain,(
    ! [A_542,B_543,C_544] :
      ( k1_xboole_0 = A_542
      | k1_relset_1(B_543,A_542,k2_funct_1(C_544)) = B_543
      | ~ v1_funct_2(k2_funct_1(C_544),B_543,A_542)
      | k2_relset_1(A_542,B_543,C_544) != B_543
      | ~ v2_funct_1(C_544)
      | ~ m1_subset_1(C_544,k1_zfmisc_1(k2_zfmisc_1(A_542,B_543)))
      | ~ v1_funct_2(C_544,A_542,B_543)
      | ~ v1_funct_1(C_544) ) ),
    inference(resolution,[status(thm)],[c_10942,c_28])).

tff(c_12529,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_12490])).

tff(c_12574,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_10795,c_12296,c_12529])).

tff(c_12575,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_12574])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12582,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12575,c_8])).

tff(c_12591,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_70,c_54,c_12582])).

tff(c_12593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10837,c_12591])).

tff(c_12594,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_10835])).

tff(c_403,plain,(
    ! [B_103,F_105,A_104,C_106,E_107,D_102] :
      ( k1_partfun1(A_104,B_103,C_106,D_102,E_107,F_105) = k5_relat_1(E_107,F_105)
      | ~ m1_subset_1(F_105,k1_zfmisc_1(k2_zfmisc_1(C_106,D_102)))
      | ~ v1_funct_1(F_105)
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103)))
      | ~ v1_funct_1(E_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_407,plain,(
    ! [A_104,B_103,E_107] :
      ( k1_partfun1(A_104,B_103,'#skF_2','#skF_1',E_107,'#skF_4') = k5_relat_1(E_107,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103)))
      | ~ v1_funct_1(E_107) ) ),
    inference(resolution,[status(thm)],[c_60,c_403])).

tff(c_417,plain,(
    ! [A_108,B_109,E_110] :
      ( k1_partfun1(A_108,B_109,'#skF_2','#skF_1',E_110,'#skF_4') = k5_relat_1(E_110,'#skF_4')
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_1(E_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_407])).

tff(c_426,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_417])).

tff(c_433,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_426])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_193,plain,(
    ! [D_66,C_67,A_68,B_69] :
      ( D_66 = C_67
      | ~ r2_relset_1(A_68,B_69,C_67,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_200,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_193])).

tff(c_223,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_460,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_223])).

tff(c_547,plain,(
    ! [C_126,A_130,F_131,E_129,B_127,D_128] :
      ( m1_subset_1(k1_partfun1(A_130,B_127,C_126,D_128,E_129,F_131),k1_zfmisc_1(k2_zfmisc_1(A_130,D_128)))
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_126,D_128)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_127)))
      | ~ v1_funct_1(E_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_617,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_547])).

tff(c_649,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_617])).

tff(c_651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_649])).

tff(c_652,plain,
    ( ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_695,plain,(
    ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_209,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_funct_1(k2_funct_1(C_70))
      | k2_relset_1(A_71,B_72,C_70) != B_72
      | ~ v2_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_70,A_71,B_72)
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_215,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_209])).

tff(c_221,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_215])).

tff(c_38,plain,(
    ! [C_35,B_34,A_33] :
      ( m1_subset_1(k2_funct_1(C_35),k1_zfmisc_1(k2_zfmisc_1(B_34,A_33)))
      | k2_relset_1(A_33,B_34,C_35) != B_34
      | ~ v2_funct_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2899,plain,(
    ! [B_243,C_244,A_245] :
      ( k6_partfun1(B_243) = k5_relat_1(k2_funct_1(C_244),C_244)
      | k1_xboole_0 = B_243
      | ~ v2_funct_1(C_244)
      | k2_relset_1(A_245,B_243,C_244) != B_243
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_243)))
      | ~ v1_funct_2(C_244,A_245,B_243)
      | ~ v1_funct_1(C_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2907,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2899])).

tff(c_2919,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_2907])).

tff(c_2920,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2919])).

tff(c_2615,plain,(
    ! [E_227,C_226,F_225,A_224,D_222,B_223] :
      ( k1_partfun1(A_224,B_223,C_226,D_222,E_227,F_225) = k5_relat_1(E_227,F_225)
      | ~ m1_subset_1(F_225,k1_zfmisc_1(k2_zfmisc_1(C_226,D_222)))
      | ~ v1_funct_1(F_225)
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_224,B_223)))
      | ~ v1_funct_1(E_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2621,plain,(
    ! [A_224,B_223,E_227] :
      ( k1_partfun1(A_224,B_223,'#skF_1','#skF_2',E_227,'#skF_3') = k5_relat_1(E_227,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_224,B_223)))
      | ~ v1_funct_1(E_227) ) ),
    inference(resolution,[status(thm)],[c_66,c_2615])).

tff(c_2865,plain,(
    ! [A_240,B_241,E_242] :
      ( k1_partfun1(A_240,B_241,'#skF_1','#skF_2',E_242,'#skF_3') = k5_relat_1(E_242,'#skF_3')
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ v1_funct_1(E_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2621])).

tff(c_9442,plain,(
    ! [B_456,A_457,C_458] :
      ( k1_partfun1(B_456,A_457,'#skF_1','#skF_2',k2_funct_1(C_458),'#skF_3') = k5_relat_1(k2_funct_1(C_458),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_458))
      | k2_relset_1(A_457,B_456,C_458) != B_456
      | ~ v2_funct_1(C_458)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_457,B_456)))
      | ~ v1_funct_2(C_458,A_457,B_456)
      | ~ v1_funct_1(C_458) ) ),
    inference(resolution,[status(thm)],[c_38,c_2865])).

tff(c_9496,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_9442])).

tff(c_9546,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_221,c_2920,c_9496])).

tff(c_2939,plain,(
    ! [E_249,A_250,D_248,B_247,F_251,C_246] :
      ( m1_subset_1(k1_partfun1(A_250,B_247,C_246,D_248,E_249,F_251),k1_zfmisc_1(k2_zfmisc_1(A_250,D_248)))
      | ~ m1_subset_1(F_251,k1_zfmisc_1(k2_zfmisc_1(C_246,D_248)))
      | ~ v1_funct_1(F_251)
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(A_250,B_247)))
      | ~ v1_funct_1(E_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3021,plain,(
    ! [E_249,A_250,D_248,B_247,F_251,C_246] :
      ( k1_xboole_0 = D_248
      | k1_relset_1(A_250,D_248,k1_partfun1(A_250,B_247,C_246,D_248,E_249,F_251)) = A_250
      | ~ v1_funct_2(k1_partfun1(A_250,B_247,C_246,D_248,E_249,F_251),A_250,D_248)
      | ~ m1_subset_1(F_251,k1_zfmisc_1(k2_zfmisc_1(C_246,D_248)))
      | ~ v1_funct_1(F_251)
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(A_250,B_247)))
      | ~ v1_funct_1(E_249) ) ),
    inference(resolution,[status(thm)],[c_2939,c_28])).

tff(c_9573,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_3'),'#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k6_partfun1('#skF_2'),'#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9546,c_3021])).

tff(c_9604,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2')) = '#skF_2'
    | ~ v1_funct_2(k6_partfun1('#skF_2'),'#skF_2','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_70,c_66,c_9546,c_9573])).

tff(c_9605,plain,
    ( k1_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2')) = '#skF_2'
    | ~ v1_funct_2(k6_partfun1('#skF_2'),'#skF_2','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_9604])).

tff(c_9613,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_9605])).

tff(c_9616,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_9613])).

tff(c_9620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_54,c_58,c_9616])).

tff(c_9622,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_9605])).

tff(c_2829,plain,(
    ! [A_237,C_238,B_239] :
      ( k6_partfun1(A_237) = k5_relat_1(C_238,k2_funct_1(C_238))
      | k1_xboole_0 = B_239
      | ~ v2_funct_1(C_238)
      | k2_relset_1(A_237,B_239,C_238) != B_239
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_237,B_239)))
      | ~ v1_funct_2(C_238,A_237,B_239)
      | ~ v1_funct_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2837,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2829])).

tff(c_2849,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_2837])).

tff(c_2850,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2849])).

tff(c_2685,plain,(
    ! [C_234,B_235,A_236] :
      ( m1_subset_1(k2_funct_1(C_234),k1_zfmisc_1(k2_zfmisc_1(B_235,A_236)))
      | k2_relset_1(A_236,B_235,C_234) != B_235
      | ~ v2_funct_1(C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_236,B_235)))
      | ~ v1_funct_2(C_234,A_236,B_235)
      | ~ v1_funct_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_34,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31) = k5_relat_1(E_30,F_31)
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5710,plain,(
    ! [B_341,A_336,E_340,C_339,A_338,B_337] :
      ( k1_partfun1(A_338,B_337,B_341,A_336,E_340,k2_funct_1(C_339)) = k5_relat_1(E_340,k2_funct_1(C_339))
      | ~ v1_funct_1(k2_funct_1(C_339))
      | ~ m1_subset_1(E_340,k1_zfmisc_1(k2_zfmisc_1(A_338,B_337)))
      | ~ v1_funct_1(E_340)
      | k2_relset_1(A_336,B_341,C_339) != B_341
      | ~ v2_funct_1(C_339)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_336,B_341)))
      | ~ v1_funct_2(C_339,A_336,B_341)
      | ~ v1_funct_1(C_339) ) ),
    inference(resolution,[status(thm)],[c_2685,c_34])).

tff(c_5742,plain,(
    ! [B_341,A_336,C_339] :
      ( k1_partfun1('#skF_1','#skF_2',B_341,A_336,'#skF_3',k2_funct_1(C_339)) = k5_relat_1('#skF_3',k2_funct_1(C_339))
      | ~ v1_funct_1(k2_funct_1(C_339))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_336,B_341,C_339) != B_341
      | ~ v2_funct_1(C_339)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_336,B_341)))
      | ~ v1_funct_2(C_339,A_336,B_341)
      | ~ v1_funct_1(C_339) ) ),
    inference(resolution,[status(thm)],[c_66,c_5710])).

tff(c_10268,plain,(
    ! [B_468,A_469,C_470] :
      ( k1_partfun1('#skF_1','#skF_2',B_468,A_469,'#skF_3',k2_funct_1(C_470)) = k5_relat_1('#skF_3',k2_funct_1(C_470))
      | ~ v1_funct_1(k2_funct_1(C_470))
      | k2_relset_1(A_469,B_468,C_470) != B_468
      | ~ v2_funct_1(C_470)
      | ~ m1_subset_1(C_470,k1_zfmisc_1(k2_zfmisc_1(A_469,B_468)))
      | ~ v1_funct_2(C_470,A_469,B_468)
      | ~ v1_funct_1(C_470) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5742])).

tff(c_10325,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_10268])).

tff(c_10378,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_221,c_2850,c_10325])).

tff(c_30,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] :
      ( m1_subset_1(k1_partfun1(A_20,B_21,C_22,D_23,E_24,F_25),k1_zfmisc_1(k2_zfmisc_1(A_20,D_23)))
      | ~ m1_subset_1(F_25,k1_zfmisc_1(k2_zfmisc_1(C_22,D_23)))
      | ~ v1_funct_1(F_25)
      | ~ m1_subset_1(E_24,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_1(E_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10704,plain,
    ( m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10378,c_30])).

tff(c_10735,plain,(
    m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_221,c_9622,c_10704])).

tff(c_10737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_695,c_10735])).

tff(c_10738,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_12743,plain,(
    ! [E_575,D_570,F_573,B_571,C_574,A_572] :
      ( k1_partfun1(A_572,B_571,C_574,D_570,E_575,F_573) = k5_relat_1(E_575,F_573)
      | ~ m1_subset_1(F_573,k1_zfmisc_1(k2_zfmisc_1(C_574,D_570)))
      | ~ v1_funct_1(F_573)
      | ~ m1_subset_1(E_575,k1_zfmisc_1(k2_zfmisc_1(A_572,B_571)))
      | ~ v1_funct_1(E_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_12747,plain,(
    ! [A_572,B_571,E_575] :
      ( k1_partfun1(A_572,B_571,'#skF_2','#skF_1',E_575,'#skF_4') = k5_relat_1(E_575,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_575,k1_zfmisc_1(k2_zfmisc_1(A_572,B_571)))
      | ~ v1_funct_1(E_575) ) ),
    inference(resolution,[status(thm)],[c_60,c_12743])).

tff(c_12759,plain,(
    ! [A_576,B_577,E_578] :
      ( k1_partfun1(A_576,B_577,'#skF_2','#skF_1',E_578,'#skF_4') = k5_relat_1(E_578,'#skF_4')
      | ~ m1_subset_1(E_578,k1_zfmisc_1(k2_zfmisc_1(A_576,B_577)))
      | ~ v1_funct_1(E_578) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_12747])).

tff(c_12768,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_12759])).

tff(c_12777,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10738,c_12768])).

tff(c_12779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12594,c_12777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.47/4.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.55/4.52  
% 11.55/4.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.55/4.52  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.55/4.52  
% 11.55/4.52  %Foreground sorts:
% 11.55/4.52  
% 11.55/4.52  
% 11.55/4.52  %Background operators:
% 11.55/4.52  
% 11.55/4.52  
% 11.55/4.52  %Foreground operators:
% 11.55/4.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.55/4.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.55/4.52  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.55/4.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.55/4.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.55/4.52  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.55/4.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.55/4.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.55/4.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.55/4.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.55/4.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.55/4.52  tff('#skF_2', type, '#skF_2': $i).
% 11.55/4.52  tff('#skF_3', type, '#skF_3': $i).
% 11.55/4.52  tff('#skF_1', type, '#skF_1': $i).
% 11.55/4.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.55/4.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.55/4.52  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.55/4.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.55/4.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.55/4.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.55/4.52  tff('#skF_4', type, '#skF_4': $i).
% 11.55/4.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.55/4.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.55/4.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.55/4.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.55/4.52  
% 11.68/4.54  tff(f_173, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 11.68/4.54  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.68/4.54  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.68/4.54  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.68/4.54  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.68/4.54  tff(f_115, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.68/4.54  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 11.68/4.54  tff(f_131, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 11.68/4.54  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 11.68/4.54  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.68/4.54  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.68/4.54  tff(f_103, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.68/4.54  tff(f_147, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 11.68/4.54  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_124, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.68/4.54  tff(c_131, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_124])).
% 11.68/4.54  tff(c_145, plain, (![B_60, A_61, C_62]: (k1_xboole_0=B_60 | k1_relset_1(A_61, B_60, C_62)=A_61 | ~v1_funct_2(C_62, A_61, B_60) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.68/4.54  tff(c_148, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_145])).
% 11.68/4.54  tff(c_154, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_131, c_148])).
% 11.68/4.54  tff(c_155, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_154])).
% 11.68/4.54  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.68/4.54  tff(c_86, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.68/4.54  tff(c_89, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_86])).
% 11.68/4.54  tff(c_95, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_89])).
% 11.68/4.54  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_92, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_86])).
% 11.68/4.54  tff(c_98, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_92])).
% 11.68/4.54  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_132, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_124])).
% 11.68/4.54  tff(c_151, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_145])).
% 11.68/4.54  tff(c_158, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_132, c_151])).
% 11.68/4.54  tff(c_159, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_158])).
% 11.68/4.54  tff(c_36, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.68/4.54  tff(c_10, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_relat_1(k1_relat_1(A_7))!=k5_relat_1(A_7, B_9) | k2_relat_1(A_7)!=k1_relat_1(B_9) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.68/4.54  tff(c_654, plain, (![A_132, B_133]: (k2_funct_1(A_132)=B_133 | k6_partfun1(k1_relat_1(A_132))!=k5_relat_1(A_132, B_133) | k2_relat_1(A_132)!=k1_relat_1(B_133) | ~v2_funct_1(A_132) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133) | ~v1_funct_1(A_132) | ~v1_relat_1(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10])).
% 11.68/4.54  tff(c_656, plain, (![B_133]: (k2_funct_1('#skF_3')=B_133 | k5_relat_1('#skF_3', B_133)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_133) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_133) | ~v1_relat_1(B_133) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_654])).
% 11.68/4.54  tff(c_10815, plain, (![B_474]: (k2_funct_1('#skF_3')=B_474 | k5_relat_1('#skF_3', B_474)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_474) | ~v1_funct_1(B_474) | ~v1_relat_1(B_474))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_70, c_54, c_656])).
% 11.68/4.54  tff(c_10824, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_95, c_10815])).
% 11.68/4.54  tff(c_10834, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_155, c_10824])).
% 11.68/4.54  tff(c_10835, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_10834])).
% 11.68/4.54  tff(c_10837, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_10835])).
% 11.68/4.54  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_10775, plain, (![C_471, B_472, A_473]: (v1_funct_2(k2_funct_1(C_471), B_472, A_473) | k2_relset_1(A_473, B_472, C_471)!=B_472 | ~v2_funct_1(C_471) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(A_473, B_472))) | ~v1_funct_2(C_471, A_473, B_472) | ~v1_funct_1(C_471))), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.68/4.54  tff(c_10787, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_10775])).
% 11.68/4.54  tff(c_10795, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_10787])).
% 11.68/4.54  tff(c_10942, plain, (![C_496, B_497, A_498]: (m1_subset_1(k2_funct_1(C_496), k1_zfmisc_1(k2_zfmisc_1(B_497, A_498))) | k2_relset_1(A_498, B_497, C_496)!=B_497 | ~v2_funct_1(C_496) | ~m1_subset_1(C_496, k1_zfmisc_1(k2_zfmisc_1(A_498, B_497))) | ~v1_funct_2(C_496, A_498, B_497) | ~v1_funct_1(C_496))), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.68/4.54  tff(c_12, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.68/4.54  tff(c_12228, plain, (![B_535, A_536, C_537]: (k1_relset_1(B_535, A_536, k2_funct_1(C_537))=k1_relat_1(k2_funct_1(C_537)) | k2_relset_1(A_536, B_535, C_537)!=B_535 | ~v2_funct_1(C_537) | ~m1_subset_1(C_537, k1_zfmisc_1(k2_zfmisc_1(A_536, B_535))) | ~v1_funct_2(C_537, A_536, B_535) | ~v1_funct_1(C_537))), inference(resolution, [status(thm)], [c_10942, c_12])).
% 11.68/4.54  tff(c_12264, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_12228])).
% 11.68/4.54  tff(c_12296, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_12264])).
% 11.68/4.54  tff(c_28, plain, (![B_18, A_17, C_19]: (k1_xboole_0=B_18 | k1_relset_1(A_17, B_18, C_19)=A_17 | ~v1_funct_2(C_19, A_17, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.68/4.54  tff(c_12490, plain, (![A_542, B_543, C_544]: (k1_xboole_0=A_542 | k1_relset_1(B_543, A_542, k2_funct_1(C_544))=B_543 | ~v1_funct_2(k2_funct_1(C_544), B_543, A_542) | k2_relset_1(A_542, B_543, C_544)!=B_543 | ~v2_funct_1(C_544) | ~m1_subset_1(C_544, k1_zfmisc_1(k2_zfmisc_1(A_542, B_543))) | ~v1_funct_2(C_544, A_542, B_543) | ~v1_funct_1(C_544))), inference(resolution, [status(thm)], [c_10942, c_28])).
% 11.68/4.54  tff(c_12529, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_12490])).
% 11.68/4.54  tff(c_12574, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_10795, c_12296, c_12529])).
% 11.68/4.54  tff(c_12575, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_12574])).
% 11.68/4.54  tff(c_8, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.68/4.54  tff(c_12582, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12575, c_8])).
% 11.68/4.54  tff(c_12591, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_70, c_54, c_12582])).
% 11.68/4.54  tff(c_12593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10837, c_12591])).
% 11.68/4.54  tff(c_12594, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_10835])).
% 11.68/4.54  tff(c_403, plain, (![B_103, F_105, A_104, C_106, E_107, D_102]: (k1_partfun1(A_104, B_103, C_106, D_102, E_107, F_105)=k5_relat_1(E_107, F_105) | ~m1_subset_1(F_105, k1_zfmisc_1(k2_zfmisc_1(C_106, D_102))) | ~v1_funct_1(F_105) | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))) | ~v1_funct_1(E_107))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.68/4.54  tff(c_407, plain, (![A_104, B_103, E_107]: (k1_partfun1(A_104, B_103, '#skF_2', '#skF_1', E_107, '#skF_4')=k5_relat_1(E_107, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))) | ~v1_funct_1(E_107))), inference(resolution, [status(thm)], [c_60, c_403])).
% 11.68/4.54  tff(c_417, plain, (![A_108, B_109, E_110]: (k1_partfun1(A_108, B_109, '#skF_2', '#skF_1', E_110, '#skF_4')=k5_relat_1(E_110, '#skF_4') | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_1(E_110))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_407])).
% 11.68/4.54  tff(c_426, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_417])).
% 11.68/4.54  tff(c_433, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_426])).
% 11.68/4.54  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.68/4.54  tff(c_193, plain, (![D_66, C_67, A_68, B_69]: (D_66=C_67 | ~r2_relset_1(A_68, B_69, C_67, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.68/4.54  tff(c_200, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_193])).
% 11.68/4.54  tff(c_223, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_200])).
% 11.68/4.54  tff(c_460, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_223])).
% 11.68/4.54  tff(c_547, plain, (![C_126, A_130, F_131, E_129, B_127, D_128]: (m1_subset_1(k1_partfun1(A_130, B_127, C_126, D_128, E_129, F_131), k1_zfmisc_1(k2_zfmisc_1(A_130, D_128))) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_126, D_128))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_127))) | ~v1_funct_1(E_129))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.68/4.54  tff(c_617, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_433, c_547])).
% 11.68/4.54  tff(c_649, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_617])).
% 11.68/4.54  tff(c_651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_460, c_649])).
% 11.68/4.54  tff(c_652, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_200])).
% 11.68/4.54  tff(c_695, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_652])).
% 11.68/4.54  tff(c_209, plain, (![C_70, A_71, B_72]: (v1_funct_1(k2_funct_1(C_70)) | k2_relset_1(A_71, B_72, C_70)!=B_72 | ~v2_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_funct_2(C_70, A_71, B_72) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.68/4.54  tff(c_215, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_209])).
% 11.68/4.54  tff(c_221, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_215])).
% 11.68/4.54  tff(c_38, plain, (![C_35, B_34, A_33]: (m1_subset_1(k2_funct_1(C_35), k1_zfmisc_1(k2_zfmisc_1(B_34, A_33))) | k2_relset_1(A_33, B_34, C_35)!=B_34 | ~v2_funct_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(C_35, A_33, B_34) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.68/4.54  tff(c_2899, plain, (![B_243, C_244, A_245]: (k6_partfun1(B_243)=k5_relat_1(k2_funct_1(C_244), C_244) | k1_xboole_0=B_243 | ~v2_funct_1(C_244) | k2_relset_1(A_245, B_243, C_244)!=B_243 | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_245, B_243))) | ~v1_funct_2(C_244, A_245, B_243) | ~v1_funct_1(C_244))), inference(cnfTransformation, [status(thm)], [f_147])).
% 11.68/4.54  tff(c_2907, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2899])).
% 11.68/4.54  tff(c_2919, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_2907])).
% 11.68/4.54  tff(c_2920, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_2919])).
% 11.68/4.54  tff(c_2615, plain, (![E_227, C_226, F_225, A_224, D_222, B_223]: (k1_partfun1(A_224, B_223, C_226, D_222, E_227, F_225)=k5_relat_1(E_227, F_225) | ~m1_subset_1(F_225, k1_zfmisc_1(k2_zfmisc_1(C_226, D_222))) | ~v1_funct_1(F_225) | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_224, B_223))) | ~v1_funct_1(E_227))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.68/4.54  tff(c_2621, plain, (![A_224, B_223, E_227]: (k1_partfun1(A_224, B_223, '#skF_1', '#skF_2', E_227, '#skF_3')=k5_relat_1(E_227, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_224, B_223))) | ~v1_funct_1(E_227))), inference(resolution, [status(thm)], [c_66, c_2615])).
% 11.68/4.54  tff(c_2865, plain, (![A_240, B_241, E_242]: (k1_partfun1(A_240, B_241, '#skF_1', '#skF_2', E_242, '#skF_3')=k5_relat_1(E_242, '#skF_3') | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~v1_funct_1(E_242))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2621])).
% 11.68/4.54  tff(c_9442, plain, (![B_456, A_457, C_458]: (k1_partfun1(B_456, A_457, '#skF_1', '#skF_2', k2_funct_1(C_458), '#skF_3')=k5_relat_1(k2_funct_1(C_458), '#skF_3') | ~v1_funct_1(k2_funct_1(C_458)) | k2_relset_1(A_457, B_456, C_458)!=B_456 | ~v2_funct_1(C_458) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_457, B_456))) | ~v1_funct_2(C_458, A_457, B_456) | ~v1_funct_1(C_458))), inference(resolution, [status(thm)], [c_38, c_2865])).
% 11.68/4.54  tff(c_9496, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_9442])).
% 11.68/4.54  tff(c_9546, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_221, c_2920, c_9496])).
% 11.68/4.54  tff(c_2939, plain, (![E_249, A_250, D_248, B_247, F_251, C_246]: (m1_subset_1(k1_partfun1(A_250, B_247, C_246, D_248, E_249, F_251), k1_zfmisc_1(k2_zfmisc_1(A_250, D_248))) | ~m1_subset_1(F_251, k1_zfmisc_1(k2_zfmisc_1(C_246, D_248))) | ~v1_funct_1(F_251) | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(A_250, B_247))) | ~v1_funct_1(E_249))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.68/4.54  tff(c_3021, plain, (![E_249, A_250, D_248, B_247, F_251, C_246]: (k1_xboole_0=D_248 | k1_relset_1(A_250, D_248, k1_partfun1(A_250, B_247, C_246, D_248, E_249, F_251))=A_250 | ~v1_funct_2(k1_partfun1(A_250, B_247, C_246, D_248, E_249, F_251), A_250, D_248) | ~m1_subset_1(F_251, k1_zfmisc_1(k2_zfmisc_1(C_246, D_248))) | ~v1_funct_1(F_251) | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(A_250, B_247))) | ~v1_funct_1(E_249))), inference(resolution, [status(thm)], [c_2939, c_28])).
% 11.68/4.54  tff(c_9573, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'))='#skF_2' | ~v1_funct_2(k6_partfun1('#skF_2'), '#skF_2', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9546, c_3021])).
% 11.68/4.54  tff(c_9604, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'))='#skF_2' | ~v1_funct_2(k6_partfun1('#skF_2'), '#skF_2', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_70, c_66, c_9546, c_9573])).
% 11.68/4.54  tff(c_9605, plain, (k1_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'))='#skF_2' | ~v1_funct_2(k6_partfun1('#skF_2'), '#skF_2', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_9604])).
% 11.68/4.54  tff(c_9613, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_9605])).
% 11.68/4.54  tff(c_9616, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_9613])).
% 11.68/4.54  tff(c_9620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_54, c_58, c_9616])).
% 11.68/4.54  tff(c_9622, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_9605])).
% 11.68/4.54  tff(c_2829, plain, (![A_237, C_238, B_239]: (k6_partfun1(A_237)=k5_relat_1(C_238, k2_funct_1(C_238)) | k1_xboole_0=B_239 | ~v2_funct_1(C_238) | k2_relset_1(A_237, B_239, C_238)!=B_239 | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_237, B_239))) | ~v1_funct_2(C_238, A_237, B_239) | ~v1_funct_1(C_238))), inference(cnfTransformation, [status(thm)], [f_147])).
% 11.68/4.54  tff(c_2837, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2829])).
% 11.68/4.54  tff(c_2849, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_2837])).
% 11.68/4.54  tff(c_2850, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_2849])).
% 11.68/4.54  tff(c_2685, plain, (![C_234, B_235, A_236]: (m1_subset_1(k2_funct_1(C_234), k1_zfmisc_1(k2_zfmisc_1(B_235, A_236))) | k2_relset_1(A_236, B_235, C_234)!=B_235 | ~v2_funct_1(C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_236, B_235))) | ~v1_funct_2(C_234, A_236, B_235) | ~v1_funct_1(C_234))), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.68/4.54  tff(c_34, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31)=k5_relat_1(E_30, F_31) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.68/4.54  tff(c_5710, plain, (![B_341, A_336, E_340, C_339, A_338, B_337]: (k1_partfun1(A_338, B_337, B_341, A_336, E_340, k2_funct_1(C_339))=k5_relat_1(E_340, k2_funct_1(C_339)) | ~v1_funct_1(k2_funct_1(C_339)) | ~m1_subset_1(E_340, k1_zfmisc_1(k2_zfmisc_1(A_338, B_337))) | ~v1_funct_1(E_340) | k2_relset_1(A_336, B_341, C_339)!=B_341 | ~v2_funct_1(C_339) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_336, B_341))) | ~v1_funct_2(C_339, A_336, B_341) | ~v1_funct_1(C_339))), inference(resolution, [status(thm)], [c_2685, c_34])).
% 11.68/4.54  tff(c_5742, plain, (![B_341, A_336, C_339]: (k1_partfun1('#skF_1', '#skF_2', B_341, A_336, '#skF_3', k2_funct_1(C_339))=k5_relat_1('#skF_3', k2_funct_1(C_339)) | ~v1_funct_1(k2_funct_1(C_339)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_336, B_341, C_339)!=B_341 | ~v2_funct_1(C_339) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_336, B_341))) | ~v1_funct_2(C_339, A_336, B_341) | ~v1_funct_1(C_339))), inference(resolution, [status(thm)], [c_66, c_5710])).
% 11.68/4.54  tff(c_10268, plain, (![B_468, A_469, C_470]: (k1_partfun1('#skF_1', '#skF_2', B_468, A_469, '#skF_3', k2_funct_1(C_470))=k5_relat_1('#skF_3', k2_funct_1(C_470)) | ~v1_funct_1(k2_funct_1(C_470)) | k2_relset_1(A_469, B_468, C_470)!=B_468 | ~v2_funct_1(C_470) | ~m1_subset_1(C_470, k1_zfmisc_1(k2_zfmisc_1(A_469, B_468))) | ~v1_funct_2(C_470, A_469, B_468) | ~v1_funct_1(C_470))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5742])).
% 11.68/4.54  tff(c_10325, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_10268])).
% 11.68/4.54  tff(c_10378, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_221, c_2850, c_10325])).
% 11.68/4.54  tff(c_30, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (m1_subset_1(k1_partfun1(A_20, B_21, C_22, D_23, E_24, F_25), k1_zfmisc_1(k2_zfmisc_1(A_20, D_23))) | ~m1_subset_1(F_25, k1_zfmisc_1(k2_zfmisc_1(C_22, D_23))) | ~v1_funct_1(F_25) | ~m1_subset_1(E_24, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_1(E_24))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.68/4.54  tff(c_10704, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10378, c_30])).
% 11.68/4.54  tff(c_10735, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_221, c_9622, c_10704])).
% 11.68/4.54  tff(c_10737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_695, c_10735])).
% 11.68/4.54  tff(c_10738, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_652])).
% 11.68/4.54  tff(c_12743, plain, (![E_575, D_570, F_573, B_571, C_574, A_572]: (k1_partfun1(A_572, B_571, C_574, D_570, E_575, F_573)=k5_relat_1(E_575, F_573) | ~m1_subset_1(F_573, k1_zfmisc_1(k2_zfmisc_1(C_574, D_570))) | ~v1_funct_1(F_573) | ~m1_subset_1(E_575, k1_zfmisc_1(k2_zfmisc_1(A_572, B_571))) | ~v1_funct_1(E_575))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.68/4.54  tff(c_12747, plain, (![A_572, B_571, E_575]: (k1_partfun1(A_572, B_571, '#skF_2', '#skF_1', E_575, '#skF_4')=k5_relat_1(E_575, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_575, k1_zfmisc_1(k2_zfmisc_1(A_572, B_571))) | ~v1_funct_1(E_575))), inference(resolution, [status(thm)], [c_60, c_12743])).
% 11.68/4.54  tff(c_12759, plain, (![A_576, B_577, E_578]: (k1_partfun1(A_576, B_577, '#skF_2', '#skF_1', E_578, '#skF_4')=k5_relat_1(E_578, '#skF_4') | ~m1_subset_1(E_578, k1_zfmisc_1(k2_zfmisc_1(A_576, B_577))) | ~v1_funct_1(E_578))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_12747])).
% 11.68/4.54  tff(c_12768, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_12759])).
% 11.68/4.54  tff(c_12777, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10738, c_12768])).
% 11.68/4.54  tff(c_12779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12594, c_12777])).
% 11.68/4.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.68/4.54  
% 11.68/4.54  Inference rules
% 11.68/4.54  ----------------------
% 11.68/4.54  #Ref     : 0
% 11.68/4.54  #Sup     : 2413
% 11.68/4.54  #Fact    : 0
% 11.68/4.54  #Define  : 0
% 11.68/4.54  #Split   : 43
% 11.68/4.54  #Chain   : 0
% 11.68/4.54  #Close   : 0
% 11.68/4.54  
% 11.68/4.54  Ordering : KBO
% 11.68/4.54  
% 11.68/4.54  Simplification rules
% 11.68/4.54  ----------------------
% 11.68/4.54  #Subsume      : 414
% 11.68/4.54  #Demod        : 3956
% 11.68/4.54  #Tautology    : 337
% 11.68/4.54  #SimpNegUnit  : 399
% 11.68/4.54  #BackRed      : 80
% 11.68/4.54  
% 11.68/4.54  #Partial instantiations: 0
% 11.68/4.54  #Strategies tried      : 1
% 11.68/4.54  
% 11.68/4.54  Timing (in seconds)
% 11.68/4.54  ----------------------
% 11.68/4.55  Preprocessing        : 0.36
% 11.68/4.55  Parsing              : 0.19
% 11.68/4.55  CNF conversion       : 0.02
% 11.68/4.55  Main loop            : 3.36
% 11.68/4.55  Inferencing          : 0.82
% 11.68/4.55  Reduction            : 1.70
% 11.68/4.55  Demodulation         : 1.38
% 11.68/4.55  BG Simplification    : 0.07
% 11.68/4.55  Subsumption          : 0.61
% 11.68/4.55  Abstraction          : 0.12
% 11.68/4.55  MUC search           : 0.00
% 11.68/4.55  Cooper               : 0.00
% 11.68/4.55  Total                : 3.77
% 11.68/4.55  Index Insertion      : 0.00
% 11.68/4.55  Index Deletion       : 0.00
% 11.68/4.55  Index Matching       : 0.00
% 11.68/4.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
