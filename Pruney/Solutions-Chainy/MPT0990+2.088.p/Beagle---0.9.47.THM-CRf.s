%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:09 EST 2020

% Result     : Theorem 9.78s
% Output     : CNFRefutation 9.78s
% Verified   : 
% Statistics : Number of formulae       :  172 (1615 expanded)
%              Number of leaves         :   43 ( 596 expanded)
%              Depth                    :   27
%              Number of atoms          :  422 (7193 expanded)
%              Number of equality atoms :  130 (2682 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_219,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_134,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_193,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_110,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_151,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_177,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_132,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_60,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_146,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_157,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_146])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_208,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_214,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_208])).

tff(c_221,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_214])).

tff(c_196,plain,(
    ! [A_74] :
      ( k1_relat_1(k2_funct_1(A_74)) = k2_relat_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_85,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_9322,plain,(
    ! [A_457] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_457)),k2_funct_1(A_457)) = k2_funct_1(A_457)
      | ~ v1_relat_1(k2_funct_1(A_457))
      | ~ v2_funct_1(A_457)
      | ~ v1_funct_1(A_457)
      | ~ v1_relat_1(A_457) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_85])).

tff(c_9352,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_9322])).

tff(c_9372,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_82,c_66,c_9352])).

tff(c_9375,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9372])).

tff(c_9378,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_9375])).

tff(c_9382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_82,c_9378])).

tff(c_9384,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9372])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_158,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_146])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_222,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_208])).

tff(c_11501,plain,(
    ! [A_562,C_563,B_564] :
      ( k6_partfun1(A_562) = k5_relat_1(C_563,k2_funct_1(C_563))
      | k1_xboole_0 = B_564
      | ~ v2_funct_1(C_563)
      | k2_relset_1(A_562,B_564,C_563) != B_564
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(A_562,B_564)))
      | ~ v1_funct_2(C_563,A_562,B_564)
      | ~ v1_funct_1(C_563) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_11507,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_11501])).

tff(c_11517,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_222,c_11507])).

tff(c_11518,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11517])).

tff(c_11600,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_11518])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_36,plain,(
    ! [A_27] : m1_subset_1(k6_relat_1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_83,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36])).

tff(c_185,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_192,plain,(
    ! [A_27] : r2_relset_1(A_27,A_27,k6_partfun1(A_27),k6_partfun1(A_27)) ),
    inference(resolution,[status(thm)],[c_83,c_185])).

tff(c_10513,plain,(
    ! [E_508,B_511,C_510,A_509,F_507,D_512] :
      ( m1_subset_1(k1_partfun1(A_509,B_511,C_510,D_512,E_508,F_507),k1_zfmisc_1(k2_zfmisc_1(A_509,D_512)))
      | ~ m1_subset_1(F_507,k1_zfmisc_1(k2_zfmisc_1(C_510,D_512)))
      | ~ v1_funct_1(F_507)
      | ~ m1_subset_1(E_508,k1_zfmisc_1(k2_zfmisc_1(A_509,B_511)))
      | ~ v1_funct_1(E_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_9385,plain,(
    ! [D_458,C_459,A_460,B_461] :
      ( D_458 = C_459
      | ~ r2_relset_1(A_460,B_461,C_459,D_458)
      | ~ m1_subset_1(D_458,k1_zfmisc_1(k2_zfmisc_1(A_460,B_461)))
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(A_460,B_461))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_9393,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_9385])).

tff(c_9408,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_9393])).

tff(c_9499,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_9408])).

tff(c_10533,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10513,c_9499])).

tff(c_10552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_10533])).

tff(c_10553,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_9408])).

tff(c_12242,plain,(
    ! [A_591,B_592,C_593,D_594] :
      ( k2_relset_1(A_591,B_592,C_593) = B_592
      | ~ r2_relset_1(B_592,B_592,k1_partfun1(B_592,A_591,A_591,B_592,D_594,C_593),k6_partfun1(B_592))
      | ~ m1_subset_1(D_594,k1_zfmisc_1(k2_zfmisc_1(B_592,A_591)))
      | ~ v1_funct_2(D_594,B_592,A_591)
      | ~ v1_funct_1(D_594)
      | ~ m1_subset_1(C_593,k1_zfmisc_1(k2_zfmisc_1(A_591,B_592)))
      | ~ v1_funct_2(C_593,A_591,B_592)
      | ~ v1_funct_1(C_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_12248,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10553,c_12242])).

tff(c_12252,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_82,c_80,c_78,c_192,c_222,c_12248])).

tff(c_12254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11600,c_12252])).

tff(c_12256,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11518])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_relat_1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_partfun1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_12276,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12256,c_84])).

tff(c_12290,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_12276])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_11505,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_11501])).

tff(c_11513,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_70,c_66,c_11505])).

tff(c_11514,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_11513])).

tff(c_12257,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12256,c_222])).

tff(c_12353,plain,(
    ! [B_595,C_596,A_597] :
      ( k6_partfun1(B_595) = k5_relat_1(k2_funct_1(C_596),C_596)
      | k1_xboole_0 = B_595
      | ~ v2_funct_1(C_596)
      | k2_relset_1(A_597,B_595,C_596) != B_595
      | ~ m1_subset_1(C_596,k1_zfmisc_1(k2_zfmisc_1(A_597,B_595)))
      | ~ v1_funct_2(C_596,A_597,B_595)
      | ~ v1_funct_1(C_596) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_12359,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_12353])).

tff(c_12369,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_12257,c_12359])).

tff(c_12370,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_12369])).

tff(c_12490,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12370])).

tff(c_10985,plain,(
    ! [F_516,D_521,C_519,B_520,A_518,E_517] :
      ( v1_funct_1(k1_partfun1(A_518,B_520,C_519,D_521,E_517,F_516))
      | ~ m1_subset_1(F_516,k1_zfmisc_1(k2_zfmisc_1(C_519,D_521)))
      | ~ v1_funct_1(F_516)
      | ~ m1_subset_1(E_517,k1_zfmisc_1(k2_zfmisc_1(A_518,B_520)))
      | ~ v1_funct_1(E_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_10991,plain,(
    ! [A_518,B_520,E_517] :
      ( v1_funct_1(k1_partfun1(A_518,B_520,'#skF_2','#skF_1',E_517,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_517,k1_zfmisc_1(k2_zfmisc_1(A_518,B_520)))
      | ~ v1_funct_1(E_517) ) ),
    inference(resolution,[status(thm)],[c_72,c_10985])).

tff(c_11016,plain,(
    ! [A_525,B_526,E_527] :
      ( v1_funct_1(k1_partfun1(A_525,B_526,'#skF_2','#skF_1',E_527,'#skF_4'))
      | ~ m1_subset_1(E_527,k1_zfmisc_1(k2_zfmisc_1(A_525,B_526)))
      | ~ v1_funct_1(E_527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10991])).

tff(c_11022,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_11016])).

tff(c_11029,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_10553,c_11022])).

tff(c_4,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4])).

tff(c_26,plain,(
    ! [A_16] :
      ( k1_relat_1(k5_relat_1(A_16,k2_funct_1(A_16))) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_11537,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11514,c_26])).

tff(c_11554,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_82,c_66,c_87,c_11537])).

tff(c_156,plain,(
    ! [A_27] : v1_relat_1(k6_partfun1(A_27)) ),
    inference(resolution,[status(thm)],[c_83,c_146])).

tff(c_6,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [A_8] : k2_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_548,plain,(
    ! [B_90,A_91] :
      ( v2_funct_1(B_90)
      | k2_relat_1(B_90) != k1_relat_1(A_91)
      | ~ v2_funct_1(k5_relat_1(B_90,A_91))
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_575,plain,(
    ! [A_9] :
      ( v2_funct_1(k6_partfun1(k1_relat_1(A_9)))
      | k2_relat_1(k6_partfun1(k1_relat_1(A_9))) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(k6_partfun1(k1_relat_1(A_9)))
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_9)))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_548])).

tff(c_594,plain,(
    ! [A_9] :
      ( v2_funct_1(k6_partfun1(k1_relat_1(A_9)))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(k6_partfun1(k1_relat_1(A_9)))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_86,c_575])).

tff(c_11574,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1(k6_partfun1(k1_relat_1('#skF_3')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11554,c_594])).

tff(c_11591,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_82,c_11029,c_11554,c_66,c_11574])).

tff(c_13397,plain,(
    ! [E_631,C_634,D_633,B_632,A_635] :
      ( k1_xboole_0 = C_634
      | v2_funct_1(E_631)
      | k2_relset_1(A_635,B_632,D_633) != B_632
      | ~ v2_funct_1(k1_partfun1(A_635,B_632,B_632,C_634,D_633,E_631))
      | ~ m1_subset_1(E_631,k1_zfmisc_1(k2_zfmisc_1(B_632,C_634)))
      | ~ v1_funct_2(E_631,B_632,C_634)
      | ~ v1_funct_1(E_631)
      | ~ m1_subset_1(D_633,k1_zfmisc_1(k2_zfmisc_1(A_635,B_632)))
      | ~ v1_funct_2(D_633,A_635,B_632)
      | ~ v1_funct_1(D_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_13401,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_10553,c_13397])).

tff(c_13406,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_11591,c_70,c_13401])).

tff(c_13408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12490,c_64,c_13406])).

tff(c_13410,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_12370])).

tff(c_12255,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_11518])).

tff(c_13437,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13410,c_12255])).

tff(c_13453,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13437,c_26])).

tff(c_13468,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_76,c_13410,c_87,c_13453])).

tff(c_171,plain,(
    ! [A_69] :
      ( k2_relat_1(k2_funct_1(A_69)) = k1_relat_1(A_69)
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_177,plain,(
    ! [A_69] :
      ( k5_relat_1(k2_funct_1(A_69),k6_partfun1(k1_relat_1(A_69))) = k2_funct_1(A_69)
      | ~ v1_relat_1(k2_funct_1(A_69))
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_84])).

tff(c_13476,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13468,c_177])).

tff(c_13495,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_76,c_13410,c_13476])).

tff(c_13749,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_13495])).

tff(c_13752,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_13749])).

tff(c_13756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_76,c_13752])).

tff(c_13758,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_13495])).

tff(c_226,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_84])).

tff(c_230,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_226])).

tff(c_11445,plain,(
    ! [C_558,B_557,D_554,E_556,F_555,A_553] :
      ( k1_partfun1(A_553,B_557,C_558,D_554,E_556,F_555) = k5_relat_1(E_556,F_555)
      | ~ m1_subset_1(F_555,k1_zfmisc_1(k2_zfmisc_1(C_558,D_554)))
      | ~ v1_funct_1(F_555)
      | ~ m1_subset_1(E_556,k1_zfmisc_1(k2_zfmisc_1(A_553,B_557)))
      | ~ v1_funct_1(E_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_11451,plain,(
    ! [A_553,B_557,E_556] :
      ( k1_partfun1(A_553,B_557,'#skF_2','#skF_1',E_556,'#skF_4') = k5_relat_1(E_556,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_556,k1_zfmisc_1(k2_zfmisc_1(A_553,B_557)))
      | ~ v1_funct_1(E_556) ) ),
    inference(resolution,[status(thm)],[c_72,c_11445])).

tff(c_14146,plain,(
    ! [A_663,B_664,E_665] :
      ( k1_partfun1(A_663,B_664,'#skF_2','#skF_1',E_665,'#skF_4') = k5_relat_1(E_665,'#skF_4')
      | ~ m1_subset_1(E_665,k1_zfmisc_1(k2_zfmisc_1(A_663,B_664)))
      | ~ v1_funct_1(E_665) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_11451])).

tff(c_14161,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_14146])).

tff(c_14175,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_10553,c_14161])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14194,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14175,c_2])).

tff(c_14298,plain,(
    ! [C_670] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_670) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_670))
      | ~ v1_relat_1(C_670) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_158,c_14194])).

tff(c_22,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_13757,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_13495])).

tff(c_273,plain,(
    ! [A_81,B_82,C_83] :
      ( k5_relat_1(k5_relat_1(A_81,B_82),C_83) = k5_relat_1(A_81,k5_relat_1(B_82,C_83))
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_306,plain,(
    ! [A_9,C_83] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),k5_relat_1(A_9,C_83)) = k5_relat_1(A_9,C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(A_9)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_273])).

tff(c_323,plain,(
    ! [A_9,C_83] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),k5_relat_1(A_9,C_83)) = k5_relat_1(A_9,C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_306])).

tff(c_13768,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))),k2_funct_1('#skF_4')) = k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13757,c_323])).

tff(c_13779,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13758,c_156,c_13757,c_13768])).

tff(c_13811,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1('#skF_4')),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_13779])).

tff(c_13835,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_76,c_13410,c_12256,c_13811])).

tff(c_14310,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14298,c_13835])).

tff(c_14391,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13758,c_230,c_13437,c_14310])).

tff(c_14432,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14391,c_13437])).

tff(c_14904,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_7) = k5_relat_1('#skF_4',k5_relat_1('#skF_3',C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14432,c_2])).

tff(c_14949,plain,(
    ! [C_673] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_673) = k5_relat_1('#skF_4',k5_relat_1('#skF_3',C_673))
      | ~ v1_relat_1(C_673) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_157,c_14904])).

tff(c_9383,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_9372])).

tff(c_14975,plain,
    ( k5_relat_1('#skF_4',k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14949,c_9383])).

tff(c_15071,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9384,c_12290,c_11514,c_14975])).

tff(c_15073,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_15071])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.78/3.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.78/3.49  
% 9.78/3.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.78/3.49  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.78/3.49  
% 9.78/3.49  %Foreground sorts:
% 9.78/3.49  
% 9.78/3.49  
% 9.78/3.49  %Background operators:
% 9.78/3.49  
% 9.78/3.49  
% 9.78/3.49  %Foreground operators:
% 9.78/3.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.78/3.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.78/3.49  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.78/3.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.78/3.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.78/3.49  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.78/3.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.78/3.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.78/3.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.78/3.49  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.78/3.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.78/3.49  tff('#skF_2', type, '#skF_2': $i).
% 9.78/3.49  tff('#skF_3', type, '#skF_3': $i).
% 9.78/3.49  tff('#skF_1', type, '#skF_1': $i).
% 9.78/3.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.78/3.49  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.78/3.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.78/3.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.78/3.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.78/3.49  tff('#skF_4', type, '#skF_4': $i).
% 9.78/3.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.78/3.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.78/3.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.78/3.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.78/3.49  
% 9.78/3.51  tff(f_219, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.78/3.51  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.78/3.51  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.78/3.51  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.78/3.51  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.78/3.51  tff(f_134, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.78/3.51  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 9.78/3.51  tff(f_193, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 9.78/3.51  tff(f_110, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.78/3.51  tff(f_108, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.78/3.51  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.78/3.51  tff(f_151, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 9.78/3.51  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 9.78/3.51  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.78/3.51  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 9.78/3.51  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 9.78/3.51  tff(f_177, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 9.78/3.51  tff(f_132, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.78/3.51  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 9.78/3.51  tff(c_60, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_146, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.78/3.51  tff(c_157, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_146])).
% 9.78/3.51  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_14, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.78/3.51  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_208, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.78/3.51  tff(c_214, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_208])).
% 9.78/3.51  tff(c_221, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_214])).
% 9.78/3.51  tff(c_196, plain, (![A_74]: (k1_relat_1(k2_funct_1(A_74))=k2_relat_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.78/3.51  tff(c_44, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.78/3.51  tff(c_8, plain, (![A_9]: (k5_relat_1(k6_relat_1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.78/3.51  tff(c_85, plain, (![A_9]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 9.78/3.51  tff(c_9322, plain, (![A_457]: (k5_relat_1(k6_partfun1(k2_relat_1(A_457)), k2_funct_1(A_457))=k2_funct_1(A_457) | ~v1_relat_1(k2_funct_1(A_457)) | ~v2_funct_1(A_457) | ~v1_funct_1(A_457) | ~v1_relat_1(A_457))), inference(superposition, [status(thm), theory('equality')], [c_196, c_85])).
% 9.78/3.51  tff(c_9352, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_221, c_9322])).
% 9.78/3.51  tff(c_9372, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_82, c_66, c_9352])).
% 9.78/3.51  tff(c_9375, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_9372])).
% 9.78/3.51  tff(c_9378, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_9375])).
% 9.78/3.51  tff(c_9382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_82, c_9378])).
% 9.78/3.51  tff(c_9384, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_9372])).
% 9.78/3.51  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_158, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_146])).
% 9.78/3.51  tff(c_64, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_222, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_208])).
% 9.78/3.51  tff(c_11501, plain, (![A_562, C_563, B_564]: (k6_partfun1(A_562)=k5_relat_1(C_563, k2_funct_1(C_563)) | k1_xboole_0=B_564 | ~v2_funct_1(C_563) | k2_relset_1(A_562, B_564, C_563)!=B_564 | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(A_562, B_564))) | ~v1_funct_2(C_563, A_562, B_564) | ~v1_funct_1(C_563))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.78/3.51  tff(c_11507, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_11501])).
% 9.78/3.51  tff(c_11517, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_222, c_11507])).
% 9.78/3.51  tff(c_11518, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_11517])).
% 9.78/3.51  tff(c_11600, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_11518])).
% 9.78/3.51  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_36, plain, (![A_27]: (m1_subset_1(k6_relat_1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.78/3.51  tff(c_83, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36])).
% 9.78/3.51  tff(c_185, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.78/3.51  tff(c_192, plain, (![A_27]: (r2_relset_1(A_27, A_27, k6_partfun1(A_27), k6_partfun1(A_27)))), inference(resolution, [status(thm)], [c_83, c_185])).
% 9.78/3.51  tff(c_10513, plain, (![E_508, B_511, C_510, A_509, F_507, D_512]: (m1_subset_1(k1_partfun1(A_509, B_511, C_510, D_512, E_508, F_507), k1_zfmisc_1(k2_zfmisc_1(A_509, D_512))) | ~m1_subset_1(F_507, k1_zfmisc_1(k2_zfmisc_1(C_510, D_512))) | ~v1_funct_1(F_507) | ~m1_subset_1(E_508, k1_zfmisc_1(k2_zfmisc_1(A_509, B_511))) | ~v1_funct_1(E_508))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.78/3.51  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_9385, plain, (![D_458, C_459, A_460, B_461]: (D_458=C_459 | ~r2_relset_1(A_460, B_461, C_459, D_458) | ~m1_subset_1(D_458, k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))) | ~m1_subset_1(C_459, k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.78/3.51  tff(c_9393, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_9385])).
% 9.78/3.51  tff(c_9408, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_9393])).
% 9.78/3.51  tff(c_9499, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_9408])).
% 9.78/3.51  tff(c_10533, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10513, c_9499])).
% 9.78/3.51  tff(c_10552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_10533])).
% 9.78/3.51  tff(c_10553, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_9408])).
% 9.78/3.51  tff(c_12242, plain, (![A_591, B_592, C_593, D_594]: (k2_relset_1(A_591, B_592, C_593)=B_592 | ~r2_relset_1(B_592, B_592, k1_partfun1(B_592, A_591, A_591, B_592, D_594, C_593), k6_partfun1(B_592)) | ~m1_subset_1(D_594, k1_zfmisc_1(k2_zfmisc_1(B_592, A_591))) | ~v1_funct_2(D_594, B_592, A_591) | ~v1_funct_1(D_594) | ~m1_subset_1(C_593, k1_zfmisc_1(k2_zfmisc_1(A_591, B_592))) | ~v1_funct_2(C_593, A_591, B_592) | ~v1_funct_1(C_593))), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.78/3.51  tff(c_12248, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10553, c_12242])).
% 9.78/3.51  tff(c_12252, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_82, c_80, c_78, c_192, c_222, c_12248])).
% 9.78/3.51  tff(c_12254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11600, c_12252])).
% 9.78/3.51  tff(c_12256, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_11518])).
% 9.78/3.51  tff(c_10, plain, (![A_10]: (k5_relat_1(A_10, k6_relat_1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.78/3.51  tff(c_84, plain, (![A_10]: (k5_relat_1(A_10, k6_partfun1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 9.78/3.51  tff(c_12276, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12256, c_84])).
% 9.78/3.51  tff(c_12290, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_12276])).
% 9.78/3.51  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.78/3.51  tff(c_11505, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_11501])).
% 9.78/3.51  tff(c_11513, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_70, c_66, c_11505])).
% 9.78/3.51  tff(c_11514, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_11513])).
% 9.78/3.51  tff(c_12257, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12256, c_222])).
% 9.78/3.51  tff(c_12353, plain, (![B_595, C_596, A_597]: (k6_partfun1(B_595)=k5_relat_1(k2_funct_1(C_596), C_596) | k1_xboole_0=B_595 | ~v2_funct_1(C_596) | k2_relset_1(A_597, B_595, C_596)!=B_595 | ~m1_subset_1(C_596, k1_zfmisc_1(k2_zfmisc_1(A_597, B_595))) | ~v1_funct_2(C_596, A_597, B_595) | ~v1_funct_1(C_596))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.78/3.51  tff(c_12359, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_12353])).
% 9.78/3.51  tff(c_12369, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_12257, c_12359])).
% 9.78/3.51  tff(c_12370, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_12369])).
% 9.78/3.51  tff(c_12490, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_12370])).
% 9.78/3.51  tff(c_10985, plain, (![F_516, D_521, C_519, B_520, A_518, E_517]: (v1_funct_1(k1_partfun1(A_518, B_520, C_519, D_521, E_517, F_516)) | ~m1_subset_1(F_516, k1_zfmisc_1(k2_zfmisc_1(C_519, D_521))) | ~v1_funct_1(F_516) | ~m1_subset_1(E_517, k1_zfmisc_1(k2_zfmisc_1(A_518, B_520))) | ~v1_funct_1(E_517))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.78/3.51  tff(c_10991, plain, (![A_518, B_520, E_517]: (v1_funct_1(k1_partfun1(A_518, B_520, '#skF_2', '#skF_1', E_517, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_517, k1_zfmisc_1(k2_zfmisc_1(A_518, B_520))) | ~v1_funct_1(E_517))), inference(resolution, [status(thm)], [c_72, c_10985])).
% 9.78/3.51  tff(c_11016, plain, (![A_525, B_526, E_527]: (v1_funct_1(k1_partfun1(A_525, B_526, '#skF_2', '#skF_1', E_527, '#skF_4')) | ~m1_subset_1(E_527, k1_zfmisc_1(k2_zfmisc_1(A_525, B_526))) | ~v1_funct_1(E_527))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10991])).
% 9.78/3.51  tff(c_11022, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_11016])).
% 9.78/3.51  tff(c_11029, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_10553, c_11022])).
% 9.78/3.51  tff(c_4, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.78/3.51  tff(c_87, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4])).
% 9.78/3.51  tff(c_26, plain, (![A_16]: (k1_relat_1(k5_relat_1(A_16, k2_funct_1(A_16)))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.78/3.51  tff(c_11537, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11514, c_26])).
% 9.78/3.51  tff(c_11554, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_82, c_66, c_87, c_11537])).
% 9.78/3.51  tff(c_156, plain, (![A_27]: (v1_relat_1(k6_partfun1(A_27)))), inference(resolution, [status(thm)], [c_83, c_146])).
% 9.78/3.51  tff(c_6, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.78/3.51  tff(c_86, plain, (![A_8]: (k2_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 9.78/3.51  tff(c_548, plain, (![B_90, A_91]: (v2_funct_1(B_90) | k2_relat_1(B_90)!=k1_relat_1(A_91) | ~v2_funct_1(k5_relat_1(B_90, A_91)) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.78/3.51  tff(c_575, plain, (![A_9]: (v2_funct_1(k6_partfun1(k1_relat_1(A_9))) | k2_relat_1(k6_partfun1(k1_relat_1(A_9)))!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(k6_partfun1(k1_relat_1(A_9))) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_9))) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_85, c_548])).
% 9.78/3.51  tff(c_594, plain, (![A_9]: (v2_funct_1(k6_partfun1(k1_relat_1(A_9))) | ~v2_funct_1(A_9) | ~v1_funct_1(k6_partfun1(k1_relat_1(A_9))) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_86, c_575])).
% 9.78/3.51  tff(c_11574, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1(k6_partfun1(k1_relat_1('#skF_3'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11554, c_594])).
% 9.78/3.51  tff(c_11591, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_82, c_11029, c_11554, c_66, c_11574])).
% 9.78/3.51  tff(c_13397, plain, (![E_631, C_634, D_633, B_632, A_635]: (k1_xboole_0=C_634 | v2_funct_1(E_631) | k2_relset_1(A_635, B_632, D_633)!=B_632 | ~v2_funct_1(k1_partfun1(A_635, B_632, B_632, C_634, D_633, E_631)) | ~m1_subset_1(E_631, k1_zfmisc_1(k2_zfmisc_1(B_632, C_634))) | ~v1_funct_2(E_631, B_632, C_634) | ~v1_funct_1(E_631) | ~m1_subset_1(D_633, k1_zfmisc_1(k2_zfmisc_1(A_635, B_632))) | ~v1_funct_2(D_633, A_635, B_632) | ~v1_funct_1(D_633))), inference(cnfTransformation, [status(thm)], [f_177])).
% 9.78/3.51  tff(c_13401, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10553, c_13397])).
% 9.78/3.51  tff(c_13406, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_11591, c_70, c_13401])).
% 9.78/3.51  tff(c_13408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12490, c_64, c_13406])).
% 9.78/3.51  tff(c_13410, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_12370])).
% 9.78/3.51  tff(c_12255, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_11518])).
% 9.78/3.51  tff(c_13437, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13410, c_12255])).
% 9.78/3.51  tff(c_13453, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13437, c_26])).
% 9.78/3.51  tff(c_13468, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_76, c_13410, c_87, c_13453])).
% 9.78/3.51  tff(c_171, plain, (![A_69]: (k2_relat_1(k2_funct_1(A_69))=k1_relat_1(A_69) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.78/3.51  tff(c_177, plain, (![A_69]: (k5_relat_1(k2_funct_1(A_69), k6_partfun1(k1_relat_1(A_69)))=k2_funct_1(A_69) | ~v1_relat_1(k2_funct_1(A_69)) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_171, c_84])).
% 9.78/3.51  tff(c_13476, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13468, c_177])).
% 9.78/3.51  tff(c_13495, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_76, c_13410, c_13476])).
% 9.78/3.51  tff(c_13749, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_13495])).
% 9.78/3.51  tff(c_13752, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_13749])).
% 9.78/3.51  tff(c_13756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_76, c_13752])).
% 9.78/3.51  tff(c_13758, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_13495])).
% 9.78/3.51  tff(c_226, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_221, c_84])).
% 9.78/3.51  tff(c_230, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_226])).
% 9.78/3.51  tff(c_11445, plain, (![C_558, B_557, D_554, E_556, F_555, A_553]: (k1_partfun1(A_553, B_557, C_558, D_554, E_556, F_555)=k5_relat_1(E_556, F_555) | ~m1_subset_1(F_555, k1_zfmisc_1(k2_zfmisc_1(C_558, D_554))) | ~v1_funct_1(F_555) | ~m1_subset_1(E_556, k1_zfmisc_1(k2_zfmisc_1(A_553, B_557))) | ~v1_funct_1(E_556))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.78/3.51  tff(c_11451, plain, (![A_553, B_557, E_556]: (k1_partfun1(A_553, B_557, '#skF_2', '#skF_1', E_556, '#skF_4')=k5_relat_1(E_556, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_556, k1_zfmisc_1(k2_zfmisc_1(A_553, B_557))) | ~v1_funct_1(E_556))), inference(resolution, [status(thm)], [c_72, c_11445])).
% 9.78/3.51  tff(c_14146, plain, (![A_663, B_664, E_665]: (k1_partfun1(A_663, B_664, '#skF_2', '#skF_1', E_665, '#skF_4')=k5_relat_1(E_665, '#skF_4') | ~m1_subset_1(E_665, k1_zfmisc_1(k2_zfmisc_1(A_663, B_664))) | ~v1_funct_1(E_665))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_11451])).
% 9.78/3.51  tff(c_14161, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_14146])).
% 9.78/3.51  tff(c_14175, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_10553, c_14161])).
% 9.78/3.51  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.78/3.51  tff(c_14194, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14175, c_2])).
% 9.78/3.51  tff(c_14298, plain, (![C_670]: (k5_relat_1(k6_partfun1('#skF_1'), C_670)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_670)) | ~v1_relat_1(C_670))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_158, c_14194])).
% 9.78/3.51  tff(c_22, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.78/3.51  tff(c_13757, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_13495])).
% 9.78/3.51  tff(c_273, plain, (![A_81, B_82, C_83]: (k5_relat_1(k5_relat_1(A_81, B_82), C_83)=k5_relat_1(A_81, k5_relat_1(B_82, C_83)) | ~v1_relat_1(C_83) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.78/3.51  tff(c_306, plain, (![A_9, C_83]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), k5_relat_1(A_9, C_83))=k5_relat_1(A_9, C_83) | ~v1_relat_1(C_83) | ~v1_relat_1(A_9) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_85, c_273])).
% 9.78/3.51  tff(c_323, plain, (![A_9, C_83]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), k5_relat_1(A_9, C_83))=k5_relat_1(A_9, C_83) | ~v1_relat_1(C_83) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_306])).
% 9.78/3.51  tff(c_13768, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))), k2_funct_1('#skF_4'))=k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13757, c_323])).
% 9.78/3.51  tff(c_13779, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13758, c_156, c_13757, c_13768])).
% 9.78/3.51  tff(c_13811, plain, (k5_relat_1(k6_partfun1(k2_relat_1('#skF_4')), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22, c_13779])).
% 9.78/3.51  tff(c_13835, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_76, c_13410, c_12256, c_13811])).
% 9.78/3.51  tff(c_14310, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14298, c_13835])).
% 9.78/3.51  tff(c_14391, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13758, c_230, c_13437, c_14310])).
% 9.78/3.51  tff(c_14432, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14391, c_13437])).
% 9.78/3.51  tff(c_14904, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_2'), C_7)=k5_relat_1('#skF_4', k5_relat_1('#skF_3', C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14432, c_2])).
% 9.78/3.51  tff(c_14949, plain, (![C_673]: (k5_relat_1(k6_partfun1('#skF_2'), C_673)=k5_relat_1('#skF_4', k5_relat_1('#skF_3', C_673)) | ~v1_relat_1(C_673))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_157, c_14904])).
% 9.78/3.51  tff(c_9383, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_9372])).
% 9.78/3.51  tff(c_14975, plain, (k5_relat_1('#skF_4', k5_relat_1('#skF_3', k2_funct_1('#skF_3')))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14949, c_9383])).
% 9.78/3.51  tff(c_15071, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9384, c_12290, c_11514, c_14975])).
% 9.78/3.51  tff(c_15073, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_15071])).
% 9.78/3.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.78/3.51  
% 9.78/3.51  Inference rules
% 9.78/3.51  ----------------------
% 9.78/3.51  #Ref     : 0
% 9.78/3.51  #Sup     : 3118
% 9.78/3.51  #Fact    : 0
% 9.78/3.51  #Define  : 0
% 9.78/3.51  #Split   : 66
% 9.78/3.51  #Chain   : 0
% 9.78/3.51  #Close   : 0
% 9.78/3.51  
% 9.78/3.51  Ordering : KBO
% 9.78/3.51  
% 9.78/3.51  Simplification rules
% 9.78/3.51  ----------------------
% 9.78/3.51  #Subsume      : 188
% 9.78/3.51  #Demod        : 6367
% 9.78/3.51  #Tautology    : 1631
% 9.78/3.51  #SimpNegUnit  : 137
% 9.78/3.51  #BackRed      : 133
% 9.78/3.51  
% 9.78/3.51  #Partial instantiations: 0
% 9.78/3.51  #Strategies tried      : 1
% 9.78/3.51  
% 9.78/3.51  Timing (in seconds)
% 9.78/3.51  ----------------------
% 9.78/3.52  Preprocessing        : 0.39
% 9.78/3.52  Parsing              : 0.21
% 9.78/3.52  CNF conversion       : 0.03
% 9.78/3.52  Main loop            : 2.30
% 9.78/3.52  Inferencing          : 0.73
% 9.78/3.52  Reduction            : 0.96
% 9.78/3.52  Demodulation         : 0.74
% 9.78/3.52  BG Simplification    : 0.08
% 9.78/3.52  Subsumption          : 0.37
% 9.78/3.52  Abstraction          : 0.11
% 9.78/3.52  MUC search           : 0.00
% 9.78/3.52  Cooper               : 0.00
% 9.78/3.52  Total                : 2.74
% 9.78/3.52  Index Insertion      : 0.00
% 9.78/3.52  Index Deletion       : 0.00
% 9.78/3.52  Index Matching       : 0.00
% 9.78/3.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
