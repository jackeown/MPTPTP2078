%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:00 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.70s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 441 expanded)
%              Number of leaves         :   43 ( 175 expanded)
%              Depth                    :   13
%              Number of atoms          :  253 (1560 expanded)
%              Number of equality atoms :   94 ( 563 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_179,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_137,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_153,axiom,(
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

tff(c_60,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_124,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_136,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_124])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_135,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_124])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_50,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_134,plain,(
    ! [A_33] : v1_relat_1(k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_50,c_124])).

tff(c_54,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [A_8] : k2_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_relat_1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,(
    ! [A_56] :
      ( k5_relat_1(A_56,k6_partfun1(k2_relat_1(A_56))) = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_147,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_partfun1(A_8),k6_partfun1(A_8)) = k6_partfun1(A_8)
      | ~ v1_relat_1(k6_partfun1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_138])).

tff(c_151,plain,(
    ! [A_8] : k5_relat_1(k6_partfun1(A_8),k6_partfun1(A_8)) = k6_partfun1(A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_147])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_210,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_222,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_210])).

tff(c_503,plain,(
    ! [B_90,A_91,C_92] :
      ( k1_xboole_0 = B_90
      | k1_relset_1(A_91,B_90,C_92) = A_91
      | ~ v1_funct_2(C_92,A_91,B_90)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_509,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_503])).

tff(c_517,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_222,c_509])).

tff(c_518,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_517])).

tff(c_22,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_relat_1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_83,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_partfun1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_22])).

tff(c_8,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_282,plain,(
    ! [A_78,B_79,C_80] :
      ( k5_relat_1(k5_relat_1(A_78,B_79),C_80) = k5_relat_1(A_78,k5_relat_1(B_79,C_80))
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_315,plain,(
    ! [A_9,C_80] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),k5_relat_1(A_9,C_80)) = k5_relat_1(A_9,C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(A_9)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_282])).

tff(c_331,plain,(
    ! [A_9,C_80] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),k5_relat_1(A_9,C_80)) = k5_relat_1(A_9,C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_315])).

tff(c_530,plain,(
    ! [C_80] :
      ( k5_relat_1(k6_partfun1('#skF_1'),k5_relat_1('#skF_3',C_80)) = k5_relat_1('#skF_3',C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_331])).

tff(c_1305,plain,(
    ! [C_137] :
      ( k5_relat_1(k6_partfun1('#skF_1'),k5_relat_1('#skF_3',C_137)) = k5_relat_1('#skF_3',C_137)
      | ~ v1_relat_1(C_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_530])).

tff(c_1327,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_1305])).

tff(c_1342,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_82,c_66,c_151,c_518,c_1327])).

tff(c_1345,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1342])).

tff(c_1388,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1345])).

tff(c_1392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_82,c_1388])).

tff(c_1394,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1342])).

tff(c_198,plain,(
    ! [A_64] :
      ( k2_relat_1(k2_funct_1(A_64)) = k1_relat_1(A_64)
      | ~ v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_85,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_partfun1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_2018,plain,(
    ! [A_171] :
      ( k5_relat_1(k2_funct_1(A_171),k6_partfun1(k1_relat_1(A_171))) = k2_funct_1(A_171)
      | ~ v1_relat_1(k2_funct_1(A_171))
      | ~ v2_funct_1(A_171)
      | ~ v1_funct_1(A_171)
      | ~ v1_relat_1(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_85])).

tff(c_2040,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_2018])).

tff(c_2058,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_82,c_66,c_1394,c_2040])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_223,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_210])).

tff(c_512,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_503])).

tff(c_521,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_223,c_512])).

tff(c_522,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_521])).

tff(c_553,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_86])).

tff(c_561,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_553])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1238,plain,(
    ! [C_132,D_133,F_131,E_134,B_135,A_136] :
      ( m1_subset_1(k1_partfun1(A_136,B_135,C_132,D_133,E_134,F_131),k1_zfmisc_1(k2_zfmisc_1(A_136,D_133)))
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_132,D_133)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_136,B_135)))
      | ~ v1_funct_1(E_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_590,plain,(
    ! [D_93,C_94,A_95,B_96] :
      ( D_93 = C_94
      | ~ r2_relset_1(A_95,B_96,C_94,D_93)
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_598,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_590])).

tff(c_613,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_598])).

tff(c_687,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_1253,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1238,c_687])).

tff(c_1296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_1253])).

tff(c_1297,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_1543,plain,(
    ! [B_155,F_153,C_156,D_152,E_154,A_151] :
      ( k1_partfun1(A_151,B_155,C_156,D_152,E_154,F_153) = k5_relat_1(E_154,F_153)
      | ~ m1_subset_1(F_153,k1_zfmisc_1(k2_zfmisc_1(C_156,D_152)))
      | ~ v1_funct_1(F_153)
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_151,B_155)))
      | ~ v1_funct_1(E_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1549,plain,(
    ! [A_151,B_155,E_154] :
      ( k1_partfun1(A_151,B_155,'#skF_2','#skF_1',E_154,'#skF_4') = k5_relat_1(E_154,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_151,B_155)))
      | ~ v1_funct_1(E_154) ) ),
    inference(resolution,[status(thm)],[c_72,c_1543])).

tff(c_2061,plain,(
    ! [A_172,B_173,E_174] :
      ( k1_partfun1(A_172,B_173,'#skF_2','#skF_1',E_174,'#skF_4') = k5_relat_1(E_174,'#skF_4')
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_1(E_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1549])).

tff(c_2067,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2061])).

tff(c_2074,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1297,c_2067])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2244,plain,(
    ! [B_175,C_176,A_177] :
      ( k6_partfun1(B_175) = k5_relat_1(k2_funct_1(C_176),C_176)
      | k1_xboole_0 = B_175
      | ~ v2_funct_1(C_176)
      | k2_relset_1(A_177,B_175,C_176) != B_175
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_175)))
      | ~ v1_funct_2(C_176,A_177,B_175)
      | ~ v1_funct_1(C_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2248,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2244])).

tff(c_2254,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_70,c_66,c_2248])).

tff(c_2255,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2254])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2269,plain,(
    ! [C_7] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_7)) = k5_relat_1(k6_partfun1('#skF_2'),C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2255,c_2])).

tff(c_3849,plain,(
    ! [C_209] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_209)) = k5_relat_1(k6_partfun1('#skF_2'),C_209)
      | ~ v1_relat_1(C_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_135,c_2269])).

tff(c_3900,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2074,c_3849])).

tff(c_3941,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_2058,c_561,c_3900])).

tff(c_3943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/2.09  
% 5.51/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/2.09  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.51/2.09  
% 5.51/2.09  %Foreground sorts:
% 5.51/2.09  
% 5.51/2.09  
% 5.51/2.09  %Background operators:
% 5.51/2.09  
% 5.51/2.09  
% 5.51/2.09  %Foreground operators:
% 5.51/2.09  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.51/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.51/2.09  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.51/2.09  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.51/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.51/2.09  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.51/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.51/2.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.51/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.51/2.09  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.51/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.51/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.51/2.09  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.51/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.51/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.51/2.09  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.51/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.51/2.09  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.51/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.51/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.51/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.51/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.51/2.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.51/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.51/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.51/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.51/2.09  
% 5.70/2.11  tff(f_179, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 5.70/2.11  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.70/2.11  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.70/2.11  tff(f_125, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.70/2.11  tff(f_137, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.70/2.11  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.70/2.11  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 5.70/2.11  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.70/2.11  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.70/2.11  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.70/2.11  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 5.70/2.11  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 5.70/2.11  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.70/2.11  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.70/2.11  tff(f_91, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.70/2.11  tff(f_135, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.70/2.11  tff(f_153, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 5.70/2.11  tff(c_60, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_124, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.70/2.11  tff(c_136, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_124])).
% 5.70/2.11  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_135, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_124])).
% 5.70/2.11  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_14, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.70/2.11  tff(c_50, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.70/2.11  tff(c_134, plain, (![A_33]: (v1_relat_1(k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_50, c_124])).
% 5.70/2.11  tff(c_54, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.70/2.11  tff(c_6, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.70/2.11  tff(c_87, plain, (![A_8]: (k2_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6])).
% 5.70/2.11  tff(c_10, plain, (![A_10]: (k5_relat_1(A_10, k6_relat_1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.70/2.11  tff(c_138, plain, (![A_56]: (k5_relat_1(A_56, k6_partfun1(k2_relat_1(A_56)))=A_56 | ~v1_relat_1(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_10])).
% 5.70/2.11  tff(c_147, plain, (![A_8]: (k5_relat_1(k6_partfun1(A_8), k6_partfun1(A_8))=k6_partfun1(A_8) | ~v1_relat_1(k6_partfun1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_138])).
% 5.70/2.11  tff(c_151, plain, (![A_8]: (k5_relat_1(k6_partfun1(A_8), k6_partfun1(A_8))=k6_partfun1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_147])).
% 5.70/2.11  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_210, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.70/2.11  tff(c_222, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_210])).
% 5.70/2.11  tff(c_503, plain, (![B_90, A_91, C_92]: (k1_xboole_0=B_90 | k1_relset_1(A_91, B_90, C_92)=A_91 | ~v1_funct_2(C_92, A_91, B_90) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.70/2.11  tff(c_509, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_503])).
% 5.70/2.11  tff(c_517, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_222, c_509])).
% 5.70/2.11  tff(c_518, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_517])).
% 5.70/2.11  tff(c_22, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_relat_1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.70/2.11  tff(c_83, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_partfun1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_22])).
% 5.70/2.11  tff(c_8, plain, (![A_9]: (k5_relat_1(k6_relat_1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.70/2.11  tff(c_86, plain, (![A_9]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8])).
% 5.70/2.11  tff(c_282, plain, (![A_78, B_79, C_80]: (k5_relat_1(k5_relat_1(A_78, B_79), C_80)=k5_relat_1(A_78, k5_relat_1(B_79, C_80)) | ~v1_relat_1(C_80) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.70/2.11  tff(c_315, plain, (![A_9, C_80]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), k5_relat_1(A_9, C_80))=k5_relat_1(A_9, C_80) | ~v1_relat_1(C_80) | ~v1_relat_1(A_9) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_86, c_282])).
% 5.70/2.11  tff(c_331, plain, (![A_9, C_80]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), k5_relat_1(A_9, C_80))=k5_relat_1(A_9, C_80) | ~v1_relat_1(C_80) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_315])).
% 5.70/2.11  tff(c_530, plain, (![C_80]: (k5_relat_1(k6_partfun1('#skF_1'), k5_relat_1('#skF_3', C_80))=k5_relat_1('#skF_3', C_80) | ~v1_relat_1(C_80) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_518, c_331])).
% 5.70/2.11  tff(c_1305, plain, (![C_137]: (k5_relat_1(k6_partfun1('#skF_1'), k5_relat_1('#skF_3', C_137))=k5_relat_1('#skF_3', C_137) | ~v1_relat_1(C_137))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_530])).
% 5.70/2.11  tff(c_1327, plain, (k5_relat_1(k6_partfun1('#skF_1'), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_83, c_1305])).
% 5.70/2.11  tff(c_1342, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_82, c_66, c_151, c_518, c_1327])).
% 5.70/2.11  tff(c_1345, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1342])).
% 5.70/2.11  tff(c_1388, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1345])).
% 5.70/2.11  tff(c_1392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_82, c_1388])).
% 5.70/2.11  tff(c_1394, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1342])).
% 5.70/2.11  tff(c_198, plain, (![A_64]: (k2_relat_1(k2_funct_1(A_64))=k1_relat_1(A_64) | ~v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.70/2.11  tff(c_85, plain, (![A_10]: (k5_relat_1(A_10, k6_partfun1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_10])).
% 5.70/2.11  tff(c_2018, plain, (![A_171]: (k5_relat_1(k2_funct_1(A_171), k6_partfun1(k1_relat_1(A_171)))=k2_funct_1(A_171) | ~v1_relat_1(k2_funct_1(A_171)) | ~v2_funct_1(A_171) | ~v1_funct_1(A_171) | ~v1_relat_1(A_171))), inference(superposition, [status(thm), theory('equality')], [c_198, c_85])).
% 5.70/2.11  tff(c_2040, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_518, c_2018])).
% 5.70/2.11  tff(c_2058, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_82, c_66, c_1394, c_2040])).
% 5.70/2.11  tff(c_64, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_223, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_210])).
% 5.70/2.11  tff(c_512, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_503])).
% 5.70/2.11  tff(c_521, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_223, c_512])).
% 5.70/2.11  tff(c_522, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_64, c_521])).
% 5.70/2.11  tff(c_553, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_522, c_86])).
% 5.70/2.11  tff(c_561, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_553])).
% 5.70/2.11  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_1238, plain, (![C_132, D_133, F_131, E_134, B_135, A_136]: (m1_subset_1(k1_partfun1(A_136, B_135, C_132, D_133, E_134, F_131), k1_zfmisc_1(k2_zfmisc_1(A_136, D_133))) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_132, D_133))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_136, B_135))) | ~v1_funct_1(E_134))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.70/2.11  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_590, plain, (![D_93, C_94, A_95, B_96]: (D_93=C_94 | ~r2_relset_1(A_95, B_96, C_94, D_93) | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.70/2.11  tff(c_598, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_590])).
% 5.70/2.11  tff(c_613, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_598])).
% 5.70/2.11  tff(c_687, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_613])).
% 5.70/2.11  tff(c_1253, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1238, c_687])).
% 5.70/2.11  tff(c_1296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_1253])).
% 5.70/2.11  tff(c_1297, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_613])).
% 5.70/2.11  tff(c_1543, plain, (![B_155, F_153, C_156, D_152, E_154, A_151]: (k1_partfun1(A_151, B_155, C_156, D_152, E_154, F_153)=k5_relat_1(E_154, F_153) | ~m1_subset_1(F_153, k1_zfmisc_1(k2_zfmisc_1(C_156, D_152))) | ~v1_funct_1(F_153) | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_151, B_155))) | ~v1_funct_1(E_154))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.70/2.11  tff(c_1549, plain, (![A_151, B_155, E_154]: (k1_partfun1(A_151, B_155, '#skF_2', '#skF_1', E_154, '#skF_4')=k5_relat_1(E_154, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_151, B_155))) | ~v1_funct_1(E_154))), inference(resolution, [status(thm)], [c_72, c_1543])).
% 5.70/2.11  tff(c_2061, plain, (![A_172, B_173, E_174]: (k1_partfun1(A_172, B_173, '#skF_2', '#skF_1', E_174, '#skF_4')=k5_relat_1(E_174, '#skF_4') | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_1(E_174))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1549])).
% 5.70/2.11  tff(c_2067, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2061])).
% 5.70/2.11  tff(c_2074, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1297, c_2067])).
% 5.70/2.11  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.70/2.11  tff(c_2244, plain, (![B_175, C_176, A_177]: (k6_partfun1(B_175)=k5_relat_1(k2_funct_1(C_176), C_176) | k1_xboole_0=B_175 | ~v2_funct_1(C_176) | k2_relset_1(A_177, B_175, C_176)!=B_175 | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_177, B_175))) | ~v1_funct_2(C_176, A_177, B_175) | ~v1_funct_1(C_176))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.70/2.11  tff(c_2248, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2244])).
% 5.70/2.11  tff(c_2254, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_70, c_66, c_2248])).
% 5.70/2.11  tff(c_2255, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_2254])).
% 5.70/2.11  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.70/2.11  tff(c_2269, plain, (![C_7]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_7))=k5_relat_1(k6_partfun1('#skF_2'), C_7) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2255, c_2])).
% 5.70/2.11  tff(c_3849, plain, (![C_209]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_209))=k5_relat_1(k6_partfun1('#skF_2'), C_209) | ~v1_relat_1(C_209))), inference(demodulation, [status(thm), theory('equality')], [c_1394, c_135, c_2269])).
% 5.70/2.11  tff(c_3900, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2074, c_3849])).
% 5.70/2.11  tff(c_3941, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_2058, c_561, c_3900])).
% 5.70/2.11  tff(c_3943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_3941])).
% 5.70/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.11  
% 5.70/2.11  Inference rules
% 5.70/2.11  ----------------------
% 5.70/2.11  #Ref     : 0
% 5.70/2.11  #Sup     : 824
% 5.70/2.11  #Fact    : 0
% 5.70/2.11  #Define  : 0
% 5.70/2.11  #Split   : 8
% 5.70/2.11  #Chain   : 0
% 5.70/2.11  #Close   : 0
% 5.70/2.11  
% 5.70/2.11  Ordering : KBO
% 5.70/2.11  
% 5.70/2.11  Simplification rules
% 5.70/2.11  ----------------------
% 5.70/2.11  #Subsume      : 31
% 5.70/2.11  #Demod        : 1323
% 5.70/2.11  #Tautology    : 394
% 5.70/2.11  #SimpNegUnit  : 29
% 5.70/2.11  #BackRed      : 14
% 5.70/2.11  
% 5.70/2.11  #Partial instantiations: 0
% 5.70/2.11  #Strategies tried      : 1
% 5.70/2.11  
% 5.70/2.11  Timing (in seconds)
% 5.70/2.11  ----------------------
% 5.70/2.12  Preprocessing        : 0.38
% 5.70/2.12  Parsing              : 0.21
% 5.70/2.12  CNF conversion       : 0.02
% 5.70/2.12  Main loop            : 0.91
% 5.70/2.12  Inferencing          : 0.30
% 5.70/2.12  Reduction            : 0.37
% 5.70/2.12  Demodulation         : 0.28
% 5.70/2.12  BG Simplification    : 0.04
% 5.70/2.12  Subsumption          : 0.14
% 5.70/2.12  Abstraction          : 0.05
% 5.70/2.12  MUC search           : 0.00
% 5.70/2.12  Cooper               : 0.00
% 5.70/2.12  Total                : 1.33
% 5.70/2.12  Index Insertion      : 0.00
% 5.70/2.12  Index Deletion       : 0.00
% 5.70/2.12  Index Matching       : 0.00
% 5.70/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
