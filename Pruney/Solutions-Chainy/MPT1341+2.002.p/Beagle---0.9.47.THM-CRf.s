%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:46 EST 2020

% Result     : Theorem 6.78s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :  389 (111910 expanded)
%              Number of leaves         :   39 (39322 expanded)
%              Depth                    :   23
%              Number of atoms          : 1043 (350439 expanded)
%              Number of equality atoms :  416 (140773 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_partfun1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(A),C,k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k6_partfun1(k1_relset_1(u1_struct_0(A),u1_struct_0(B),C))
                    & k1_partfun1(u1_struct_0(B),u1_struct_0(A),u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),C) = k6_partfun1(k2_relset_1(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_2)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_115,axiom,(
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

tff(f_83,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_58,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_71,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_79,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_71])).

tff(c_56,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_78,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_71])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_95,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_78,c_50])).

tff(c_96,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_96])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_46,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_80,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_52])).

tff(c_94,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_80])).

tff(c_119,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_123,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_119])).

tff(c_2297,plain,(
    ! [B_330,A_331,C_332] :
      ( k1_xboole_0 = B_330
      | k1_relset_1(A_331,B_330,C_332) = A_331
      | ~ v1_funct_2(C_332,A_331,B_330)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_331,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2300,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_95,c_2297])).

tff(c_2303,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_123,c_2300])).

tff(c_2304,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2303])).

tff(c_2308,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2304,c_94])).

tff(c_48,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_89,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_78,c_48])).

tff(c_2309,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2304,c_89])).

tff(c_2307,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2304,c_95])).

tff(c_2362,plain,(
    ! [C_339,B_340,A_341] :
      ( v1_funct_2(k2_funct_1(C_339),B_340,A_341)
      | k2_relset_1(A_341,B_340,C_339) != B_340
      | ~ v2_funct_1(C_339)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_341,B_340)))
      | ~ v1_funct_2(C_339,A_341,B_340)
      | ~ v1_funct_1(C_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2365,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2307,c_2362])).

tff(c_2368,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2308,c_46,c_2309,c_2365])).

tff(c_2403,plain,(
    ! [C_354,B_355,A_356] :
      ( m1_subset_1(k2_funct_1(C_354),k1_zfmisc_1(k2_zfmisc_1(B_355,A_356)))
      | k2_relset_1(A_356,B_355,C_354) != B_355
      | ~ v2_funct_1(C_354)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_356,B_355)))
      | ~ v1_funct_2(C_354,A_356,B_355)
      | ~ v1_funct_1(C_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( k1_relset_1(A_6,B_7,C_8) = k1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3116,plain,(
    ! [B_417,A_418,C_419] :
      ( k1_relset_1(B_417,A_418,k2_funct_1(C_419)) = k1_relat_1(k2_funct_1(C_419))
      | k2_relset_1(A_418,B_417,C_419) != B_417
      | ~ v2_funct_1(C_419)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(A_418,B_417)))
      | ~ v1_funct_2(C_419,A_418,B_417)
      | ~ v1_funct_1(C_419) ) ),
    inference(resolution,[status(thm)],[c_2403,c_12])).

tff(c_3122,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2307,c_3116])).

tff(c_3126,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2308,c_46,c_2309,c_3122])).

tff(c_24,plain,(
    ! [B_10,A_9,C_11] :
      ( k1_xboole_0 = B_10
      | k1_relset_1(A_9,B_10,C_11) = A_9
      | ~ v1_funct_2(C_11,A_9,B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3180,plain,(
    ! [A_424,B_425,C_426] :
      ( k1_xboole_0 = A_424
      | k1_relset_1(B_425,A_424,k2_funct_1(C_426)) = B_425
      | ~ v1_funct_2(k2_funct_1(C_426),B_425,A_424)
      | k2_relset_1(A_424,B_425,C_426) != B_425
      | ~ v2_funct_1(C_426)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(A_424,B_425)))
      | ~ v1_funct_2(C_426,A_424,B_425)
      | ~ v1_funct_1(C_426) ) ),
    inference(resolution,[status(thm)],[c_2403,c_24])).

tff(c_3186,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2307,c_3180])).

tff(c_3190,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2308,c_46,c_2309,c_2368,c_3126,c_3186])).

tff(c_3202,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3190])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k2_funct_1(A_1)) = k2_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3207,plain,
    ( k2_struct_0('#skF_2') = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3202,c_4])).

tff(c_3214,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_3207])).

tff(c_3230,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3214,c_2308])).

tff(c_3228,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3214,c_2307])).

tff(c_3229,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3214,c_3214,c_2309])).

tff(c_2355,plain,(
    ! [C_336,A_337,B_338] :
      ( v1_funct_1(k2_funct_1(C_336))
      | k2_relset_1(A_337,B_338,C_336) != B_338
      | ~ v2_funct_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338)))
      | ~ v1_funct_2(C_336,A_337,B_338)
      | ~ v1_funct_1(C_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2358,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2307,c_2355])).

tff(c_2361,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2308,c_46,c_2309,c_2358])).

tff(c_2465,plain,(
    ! [A_360,C_361,B_362] :
      ( k6_partfun1(A_360) = k5_relat_1(C_361,k2_funct_1(C_361))
      | k1_xboole_0 = B_362
      | ~ v2_funct_1(C_361)
      | k2_relset_1(A_360,B_362,C_361) != B_362
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_360,B_362)))
      | ~ v1_funct_2(C_361,A_360,B_362)
      | ~ v1_funct_1(C_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2469,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k2_struct_0('#skF_2') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2307,c_2465])).

tff(c_2473,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2308,c_2309,c_46,c_2469])).

tff(c_2474,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2473])).

tff(c_2484,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2474,c_2308])).

tff(c_2482,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2474,c_2307])).

tff(c_16,plain,(
    ! [C_11,A_9] :
      ( k1_xboole_0 = C_11
      | ~ v1_funct_2(C_11,A_9,k1_xboole_0)
      | k1_xboole_0 = A_9
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2530,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0)
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2482,c_16])).

tff(c_2566,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2484,c_2530])).

tff(c_2581,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2566])).

tff(c_2586,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2581,c_2484])).

tff(c_2483,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2474,c_2474,c_2309])).

tff(c_2587,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2581,c_2483])).

tff(c_2480,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k1_xboole_0,k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2474,c_2368])).

tff(c_2585,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2581,c_2480])).

tff(c_2582,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2581,c_2482])).

tff(c_2452,plain,(
    ! [B_355,A_356,C_354] :
      ( k1_relset_1(B_355,A_356,k2_funct_1(C_354)) = k1_relat_1(k2_funct_1(C_354))
      | k2_relset_1(A_356,B_355,C_354) != B_355
      | ~ v2_funct_1(C_354)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_356,B_355)))
      | ~ v1_funct_2(C_354,A_356,B_355)
      | ~ v1_funct_1(C_354) ) ),
    inference(resolution,[status(thm)],[c_2403,c_12])).

tff(c_2621,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2582,c_2452])).

tff(c_2663,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2586,c_46,c_2587,c_2621])).

tff(c_22,plain,(
    ! [B_10,C_11] :
      ( k1_relset_1(k1_xboole_0,B_10,C_11) = k1_xboole_0
      | ~ v1_funct_2(C_11,k1_xboole_0,B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2750,plain,(
    ! [A_374,C_375] :
      ( k1_relset_1(k1_xboole_0,A_374,k2_funct_1(C_375)) = k1_xboole_0
      | ~ v1_funct_2(k2_funct_1(C_375),k1_xboole_0,A_374)
      | k2_relset_1(A_374,k1_xboole_0,C_375) != k1_xboole_0
      | ~ v2_funct_1(C_375)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_374,k1_xboole_0)))
      | ~ v1_funct_2(C_375,A_374,k1_xboole_0)
      | ~ v1_funct_1(C_375) ) ),
    inference(resolution,[status(thm)],[c_2403,c_22])).

tff(c_2753,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k1_xboole_0,k1_xboole_0)
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2582,c_2750])).

tff(c_2760,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2586,c_46,c_2587,c_2585,c_2663,c_2753])).

tff(c_2766,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2760,c_4])).

tff(c_2773,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_2766])).

tff(c_28,plain,(
    ! [A_18] : k6_relat_1(A_18) = k6_partfun1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_partfun1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6])).

tff(c_2386,plain,(
    ! [B_345,C_350,D_348,A_346,E_347,F_349] :
      ( k1_partfun1(A_346,B_345,C_350,D_348,E_347,F_349) = k5_relat_1(E_347,F_349)
      | ~ m1_subset_1(F_349,k1_zfmisc_1(k2_zfmisc_1(C_350,D_348)))
      | ~ v1_funct_1(F_349)
      | ~ m1_subset_1(E_347,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345)))
      | ~ v1_funct_1(E_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2388,plain,(
    ! [A_346,B_345,E_347] :
      ( k1_partfun1(A_346,B_345,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),E_347,'#skF_3') = k5_relat_1(E_347,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_347,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345)))
      | ~ v1_funct_1(E_347) ) ),
    inference(resolution,[status(thm)],[c_2307,c_2386])).

tff(c_2391,plain,(
    ! [A_346,B_345,E_347] :
      ( k1_partfun1(A_346,B_345,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),E_347,'#skF_3') = k5_relat_1(E_347,'#skF_3')
      | ~ m1_subset_1(E_347,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345)))
      | ~ v1_funct_1(E_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2388])).

tff(c_2442,plain,(
    ! [B_355,A_356,C_354] :
      ( k1_partfun1(B_355,A_356,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_funct_1(C_354),'#skF_3') = k5_relat_1(k2_funct_1(C_354),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_354))
      | k2_relset_1(A_356,B_355,C_354) != B_355
      | ~ v2_funct_1(C_354)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_356,B_355)))
      | ~ v1_funct_2(C_354,A_356,B_355)
      | ~ v1_funct_1(C_354) ) ),
    inference(resolution,[status(thm)],[c_2403,c_2391])).

tff(c_2783,plain,(
    ! [B_376,A_377,C_378] :
      ( k1_partfun1(B_376,A_377,k1_xboole_0,k1_xboole_0,k2_funct_1(C_378),'#skF_3') = k5_relat_1(k2_funct_1(C_378),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_378))
      | k2_relset_1(A_377,B_376,C_378) != B_376
      | ~ v2_funct_1(C_378)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(A_377,B_376)))
      | ~ v1_funct_2(C_378,A_377,B_376)
      | ~ v1_funct_1(C_378) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2581,c_2474,c_2442])).

tff(c_2786,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2582,c_2783])).

tff(c_2792,plain,(
    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2586,c_46,c_2587,c_2361,c_2786])).

tff(c_2369,plain,(
    ! [A_342,B_343,C_344] :
      ( k2_tops_2(A_342,B_343,C_344) = k2_funct_1(C_344)
      | ~ v2_funct_1(C_344)
      | k2_relset_1(A_342,B_343,C_344) != B_343
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343)))
      | ~ v1_funct_2(C_344,A_342,B_343)
      | ~ v1_funct_1(C_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2372,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2307,c_2369])).

tff(c_2375,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2308,c_2309,c_46,c_2372])).

tff(c_8,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_relat_1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_partfun1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8])).

tff(c_152,plain,(
    ! [B_52,A_53,C_54] :
      ( k1_xboole_0 = B_52
      | k1_relset_1(A_53,B_52,C_54) = A_53
      | ~ v1_funct_2(C_54,A_53,B_52)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_155,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_95,c_152])).

tff(c_158,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_123,c_155])).

tff(c_159,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_162,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_94])).

tff(c_163,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_89])).

tff(c_161,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_95])).

tff(c_310,plain,(
    ! [B_82,C_83,A_84] :
      ( k6_partfun1(B_82) = k5_relat_1(k2_funct_1(C_83),C_83)
      | k1_xboole_0 = B_82
      | ~ v2_funct_1(C_83)
      | k2_relset_1(A_84,B_82,C_83) != B_82
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_82)))
      | ~ v1_funct_2(C_83,A_84,B_82)
      | ~ v1_funct_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_314,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_310])).

tff(c_318,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_162,c_163,c_46,c_314])).

tff(c_319,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_327,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_162])).

tff(c_328,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_161])).

tff(c_372,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0)
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_328,c_16])).

tff(c_411,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_372])).

tff(c_419,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_424,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_327])).

tff(c_326,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_319,c_163])).

tff(c_422,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_326])).

tff(c_202,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_funct_1(k2_funct_1(C_58))
      | k2_relset_1(A_59,B_60,C_58) != B_60
      | ~ v2_funct_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_2(C_58,A_59,B_60)
      | ~ v1_funct_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_205,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_202])).

tff(c_208,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_162,c_46,c_163,c_205])).

tff(c_421,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_328])).

tff(c_237,plain,(
    ! [C_73,B_74,A_75] :
      ( m1_subset_1(k2_funct_1(C_73),k1_zfmisc_1(k2_zfmisc_1(B_74,A_75)))
      | k2_relset_1(A_75,B_74,C_73) != B_74
      | ~ v2_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74)))
      | ~ v1_funct_2(C_73,A_75,B_74)
      | ~ v1_funct_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13] :
      ( k1_partfun1(A_12,B_13,C_14,D_15,E_16,F_17) = k5_relat_1(E_16,F_17)
      | ~ m1_subset_1(F_17,k1_zfmisc_1(k2_zfmisc_1(C_14,D_15)))
      | ~ v1_funct_1(F_17)
      | ~ m1_subset_1(E_16,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_1(E_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_673,plain,(
    ! [E_115,A_116,B_113,A_114,C_118,B_117] :
      ( k1_partfun1(A_114,B_113,B_117,A_116,E_115,k2_funct_1(C_118)) = k5_relat_1(E_115,k2_funct_1(C_118))
      | ~ v1_funct_1(k2_funct_1(C_118))
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113)))
      | ~ v1_funct_1(E_115)
      | k2_relset_1(A_116,B_117,C_118) != B_117
      | ~ v2_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_2(C_118,A_116,B_117)
      | ~ v1_funct_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_237,c_26])).

tff(c_675,plain,(
    ! [B_117,A_116,C_118] :
      ( k1_partfun1(k1_xboole_0,k1_xboole_0,B_117,A_116,'#skF_3',k2_funct_1(C_118)) = k5_relat_1('#skF_3',k2_funct_1(C_118))
      | ~ v1_funct_1(k2_funct_1(C_118))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_116,B_117,C_118) != B_117
      | ~ v2_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_2(C_118,A_116,B_117)
      | ~ v1_funct_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_421,c_673])).

tff(c_682,plain,(
    ! [B_119,A_120,C_121] :
      ( k1_partfun1(k1_xboole_0,k1_xboole_0,B_119,A_120,'#skF_3',k2_funct_1(C_121)) = k5_relat_1('#skF_3',k2_funct_1(C_121))
      | ~ v1_funct_1(k2_funct_1(C_121))
      | k2_relset_1(A_120,B_119,C_121) != B_119
      | ~ v2_funct_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(C_121,A_120,B_119)
      | ~ v1_funct_1(C_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_675])).

tff(c_685,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_421,c_682])).

tff(c_691,plain,(
    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_424,c_46,c_422,c_208,c_685])).

tff(c_219,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_tops_2(A_64,B_65,C_66) = k2_funct_1(C_66)
      | ~ v2_funct_1(C_66)
      | k2_relset_1(A_64,B_65,C_66) != B_65
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_2(C_66,A_64,B_65)
      | ~ v1_funct_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_222,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_219])).

tff(c_225,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_162,c_163,c_46,c_222])).

tff(c_44,plain,
    ( k1_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_3',k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_59,plain,
    ( k1_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2'))
    | k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_3',k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44])).

tff(c_129,plain,
    ( k1_partfun1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2'))
    | k1_partfun1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_79,c_79,c_79,c_79,c_78,c_78,c_78,c_78,c_79,c_79,c_79,c_78,c_78,c_78,c_59])).

tff(c_130,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_211,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),'#skF_3',k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_159,c_159,c_130])).

tff(c_226,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_211])).

tff(c_322,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),k1_xboole_0,k1_xboole_0,k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_319,c_226])).

tff(c_571,plain,(
    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_419,c_419,c_322])).

tff(c_693,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_571])).

tff(c_700,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) != k6_partfun1(k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_693])).

tff(c_703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_419,c_700])).

tff(c_704,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_712,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_327])).

tff(c_709,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_704,c_326])).

tff(c_708,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_328])).

tff(c_1005,plain,(
    ! [A_170,A_172,C_174,E_171,B_173,B_169] :
      ( k1_partfun1(A_170,B_169,B_173,A_172,E_171,k2_funct_1(C_174)) = k5_relat_1(E_171,k2_funct_1(C_174))
      | ~ v1_funct_1(k2_funct_1(C_174))
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169)))
      | ~ v1_funct_1(E_171)
      | k2_relset_1(A_172,B_173,C_174) != B_173
      | ~ v2_funct_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_2(C_174,A_172,B_173)
      | ~ v1_funct_1(C_174) ) ),
    inference(resolution,[status(thm)],[c_237,c_26])).

tff(c_1007,plain,(
    ! [B_173,A_172,C_174] :
      ( k1_partfun1(k1_relat_1('#skF_3'),'#skF_3',B_173,A_172,'#skF_3',k2_funct_1(C_174)) = k5_relat_1('#skF_3',k2_funct_1(C_174))
      | ~ v1_funct_1(k2_funct_1(C_174))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_172,B_173,C_174) != B_173
      | ~ v2_funct_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_2(C_174,A_172,B_173)
      | ~ v1_funct_1(C_174) ) ),
    inference(resolution,[status(thm)],[c_708,c_1005])).

tff(c_1014,plain,(
    ! [B_175,A_176,C_177] :
      ( k1_partfun1(k1_relat_1('#skF_3'),'#skF_3',B_175,A_176,'#skF_3',k2_funct_1(C_177)) = k5_relat_1('#skF_3',k2_funct_1(C_177))
      | ~ v1_funct_1(k2_funct_1(C_177))
      | k2_relset_1(A_176,B_175,C_177) != B_175
      | ~ v2_funct_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_176,B_175)))
      | ~ v1_funct_2(C_177,A_176,B_175)
      | ~ v1_funct_1(C_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1007])).

tff(c_1017,plain,
    ( k1_partfun1(k1_relat_1('#skF_3'),'#skF_3','#skF_3',k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_708,c_1014])).

tff(c_1023,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),'#skF_3','#skF_3',k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_712,c_46,c_709,c_208,c_1017])).

tff(c_822,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),'#skF_3','#skF_3',k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_704,c_322])).

tff(c_1025,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_822])).

tff(c_1032,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1025])).

tff(c_1036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_1032])).

tff(c_1038,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_212,plain,(
    ! [C_61,B_62,A_63] :
      ( v1_funct_2(k2_funct_1(C_61),B_62,A_63)
      | k2_relset_1(A_63,B_62,C_61) != B_62
      | ~ v2_funct_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62)))
      | ~ v1_funct_2(C_61,A_63,B_62)
      | ~ v1_funct_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_215,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_212])).

tff(c_218,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_162,c_46,c_163,c_215])).

tff(c_1085,plain,(
    ! [B_181,A_182,C_183] :
      ( k1_relset_1(B_181,A_182,k2_funct_1(C_183)) = k1_relat_1(k2_funct_1(C_183))
      | k2_relset_1(A_182,B_181,C_183) != B_181
      | ~ v2_funct_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_182,B_181)))
      | ~ v1_funct_2(C_183,A_182,B_181)
      | ~ v1_funct_1(C_183) ) ),
    inference(resolution,[status(thm)],[c_237,c_12])).

tff(c_1091,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_1085])).

tff(c_1095,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_162,c_46,c_163,c_1091])).

tff(c_1137,plain,(
    ! [A_191,B_192,C_193] :
      ( k1_xboole_0 = A_191
      | k1_relset_1(B_192,A_191,k2_funct_1(C_193)) = B_192
      | ~ v1_funct_2(k2_funct_1(C_193),B_192,A_191)
      | k2_relset_1(A_191,B_192,C_193) != B_192
      | ~ v2_funct_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192)))
      | ~ v1_funct_2(C_193,A_191,B_192)
      | ~ v1_funct_1(C_193) ) ),
    inference(resolution,[status(thm)],[c_237,c_24])).

tff(c_1143,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_1137])).

tff(c_1147,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_162,c_46,c_163,c_218,c_1095,c_1143])).

tff(c_1148,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1147])).

tff(c_1153,plain,
    ( k2_struct_0('#skF_2') = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1148,c_4])).

tff(c_1160,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_1153])).

tff(c_1175,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1160,c_162])).

tff(c_1176,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1160,c_161])).

tff(c_1174,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1160,c_1160,c_163])).

tff(c_1075,plain,(
    ! [A_178,C_179,B_180] :
      ( k6_partfun1(A_178) = k5_relat_1(C_179,k2_funct_1(C_179))
      | k1_xboole_0 = B_180
      | ~ v2_funct_1(C_179)
      | k2_relset_1(A_178,B_180,C_179) != B_180
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_180)))
      | ~ v1_funct_2(C_179,A_178,B_180)
      | ~ v1_funct_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1079,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k2_struct_0('#skF_2') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_1075])).

tff(c_1083,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_162,c_163,c_46,c_1079])).

tff(c_1084,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1038,c_1083])).

tff(c_1327,plain,(
    ! [E_205,A_206,B_203,A_204,B_207,C_208] :
      ( k1_partfun1(A_204,B_203,B_207,A_206,E_205,k2_funct_1(C_208)) = k5_relat_1(E_205,k2_funct_1(C_208))
      | ~ v1_funct_1(k2_funct_1(C_208))
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_1(E_205)
      | k2_relset_1(A_206,B_207,C_208) != B_207
      | ~ v2_funct_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_2(C_208,A_206,B_207)
      | ~ v1_funct_1(C_208) ) ),
    inference(resolution,[status(thm)],[c_237,c_26])).

tff(c_1329,plain,(
    ! [B_207,A_206,C_208] :
      ( k1_partfun1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),B_207,A_206,'#skF_3',k2_funct_1(C_208)) = k5_relat_1('#skF_3',k2_funct_1(C_208))
      | ~ v1_funct_1(k2_funct_1(C_208))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_206,B_207,C_208) != B_207
      | ~ v2_funct_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_2(C_208,A_206,B_207)
      | ~ v1_funct_1(C_208) ) ),
    inference(resolution,[status(thm)],[c_1176,c_1327])).

tff(c_1345,plain,(
    ! [B_212,A_213,C_214] :
      ( k1_partfun1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),B_212,A_213,'#skF_3',k2_funct_1(C_214)) = k5_relat_1('#skF_3',k2_funct_1(C_214))
      | ~ v1_funct_1(k2_funct_1(C_214))
      | k2_relset_1(A_213,B_212,C_214) != B_212
      | ~ v2_funct_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_213,B_212)))
      | ~ v1_funct_2(C_214,A_213,B_212)
      | ~ v1_funct_1(C_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1329])).

tff(c_1170,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1160,c_1160,c_226])).

tff(c_1351,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1345,c_1170])).

tff(c_1358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1175,c_1176,c_46,c_1174,c_208,c_1084,c_1351])).

tff(c_1359,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1147])).

tff(c_1371,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_162])).

tff(c_1370,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_163])).

tff(c_1368,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_218])).

tff(c_1372,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_161])).

tff(c_281,plain,(
    ! [C_73,B_74] :
      ( k2_funct_1(C_73) = k1_xboole_0
      | ~ v1_funct_2(k2_funct_1(C_73),B_74,k1_xboole_0)
      | k1_xboole_0 = B_74
      | k2_relset_1(k1_xboole_0,B_74,C_73) != B_74
      | ~ v2_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_74)))
      | ~ v1_funct_2(C_73,k1_xboole_0,B_74)
      | ~ v1_funct_1(C_73) ) ),
    inference(resolution,[status(thm)],[c_237,c_16])).

tff(c_1427,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_xboole_0)
    | k2_struct_0('#skF_2') = k1_xboole_0
    | k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1372,c_281])).

tff(c_1476,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1371,c_46,c_1370,c_1368,c_1427])).

tff(c_1477,plain,(
    k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1038,c_1476])).

tff(c_1366,plain,(
    k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_1359,c_1359,c_226])).

tff(c_1610,plain,(
    k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3',k1_xboole_0) != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1477,c_1366])).

tff(c_1527,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1477,c_208])).

tff(c_1363,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_1084])).

tff(c_1522,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1477,c_1363])).

tff(c_1557,plain,(
    ! [B_222,A_221,C_223,B_218,A_219,E_220] :
      ( k1_partfun1(A_219,B_218,B_222,A_221,E_220,k2_funct_1(C_223)) = k5_relat_1(E_220,k2_funct_1(C_223))
      | ~ v1_funct_1(k2_funct_1(C_223))
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1(A_219,B_218)))
      | ~ v1_funct_1(E_220)
      | k2_relset_1(A_221,B_222,C_223) != B_222
      | ~ v2_funct_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ v1_funct_2(C_223,A_221,B_222)
      | ~ v1_funct_1(C_223) ) ),
    inference(resolution,[status(thm)],[c_237,c_26])).

tff(c_1559,plain,(
    ! [B_222,A_221,C_223] :
      ( k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),B_222,A_221,'#skF_3',k2_funct_1(C_223)) = k5_relat_1('#skF_3',k2_funct_1(C_223))
      | ~ v1_funct_1(k2_funct_1(C_223))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_221,B_222,C_223) != B_222
      | ~ v2_funct_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ v1_funct_2(C_223,A_221,B_222)
      | ~ v1_funct_1(C_223) ) ),
    inference(resolution,[status(thm)],[c_1372,c_1557])).

tff(c_1774,plain,(
    ! [B_236,A_237,C_238] :
      ( k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),B_236,A_237,'#skF_3',k2_funct_1(C_238)) = k5_relat_1('#skF_3',k2_funct_1(C_238))
      | ~ v1_funct_1(k2_funct_1(C_238))
      | k2_relset_1(A_237,B_236,C_238) != B_236
      | ~ v2_funct_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_237,B_236)))
      | ~ v1_funct_2(C_238,A_237,B_236)
      | ~ v1_funct_1(C_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1559])).

tff(c_1780,plain,
    ( k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1372,c_1774])).

tff(c_1789,plain,(
    k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3',k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1371,c_46,c_1370,c_1527,c_1477,c_1522,c_1477,c_1477,c_1780])).

tff(c_1791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1610,c_1789])).

tff(c_1792,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_1796,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1792,c_94])).

tff(c_1795,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1792,c_95])).

tff(c_1824,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1795,c_16])).

tff(c_1840,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1796,c_1824])).

tff(c_1845,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1840])).

tff(c_1793,plain,(
    k2_struct_0('#skF_1') != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_1852,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_1793])).

tff(c_1851,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_1796])).

tff(c_1848,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_1795])).

tff(c_1878,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1848,c_22])).

tff(c_1903,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1851,c_1878])).

tff(c_1794,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1792,c_123])).

tff(c_1849,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_1794])).

tff(c_1917,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1903,c_1849])).

tff(c_1918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1852,c_1917])).

tff(c_1919,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1840])).

tff(c_1925,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1919,c_1796])).

tff(c_1797,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1792,c_1792,c_89])).

tff(c_1924,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1919,c_1919,c_1797])).

tff(c_1921,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1919,c_1795])).

tff(c_34,plain,(
    ! [C_21,A_19,B_20] :
      ( v1_funct_1(k2_funct_1(C_21))
      | k2_relset_1(A_19,B_20,C_21) != B_20
      | ~ v2_funct_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1953,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1921,c_34])).

tff(c_1962,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1925,c_46,c_1924,c_1953])).

tff(c_2037,plain,(
    ! [C_276,B_277,A_278] :
      ( m1_subset_1(k2_funct_1(C_276),k1_zfmisc_1(k2_zfmisc_1(B_277,A_278)))
      | k2_relset_1(A_278,B_277,C_276) != B_277
      | ~ v2_funct_1(C_276)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_278,B_277)))
      | ~ v1_funct_2(C_276,A_278,B_277)
      | ~ v1_funct_1(C_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2242,plain,(
    ! [A_315,A_318,B_317,C_314,E_316,B_313] :
      ( k1_partfun1(A_315,B_313,B_317,A_318,E_316,k2_funct_1(C_314)) = k5_relat_1(E_316,k2_funct_1(C_314))
      | ~ v1_funct_1(k2_funct_1(C_314))
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(A_315,B_313)))
      | ~ v1_funct_1(E_316)
      | k2_relset_1(A_318,B_317,C_314) != B_317
      | ~ v2_funct_1(C_314)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_318,B_317)))
      | ~ v1_funct_2(C_314,A_318,B_317)
      | ~ v1_funct_1(C_314) ) ),
    inference(resolution,[status(thm)],[c_2037,c_26])).

tff(c_2246,plain,(
    ! [B_317,A_318,C_314] :
      ( k1_partfun1(k2_struct_0('#skF_1'),'#skF_3',B_317,A_318,'#skF_3',k2_funct_1(C_314)) = k5_relat_1('#skF_3',k2_funct_1(C_314))
      | ~ v1_funct_1(k2_funct_1(C_314))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_318,B_317,C_314) != B_317
      | ~ v2_funct_1(C_314)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_318,B_317)))
      | ~ v1_funct_2(C_314,A_318,B_317)
      | ~ v1_funct_1(C_314) ) ),
    inference(resolution,[status(thm)],[c_1921,c_2242])).

tff(c_2251,plain,(
    ! [B_319,A_320,C_321] :
      ( k1_partfun1(k2_struct_0('#skF_1'),'#skF_3',B_319,A_320,'#skF_3',k2_funct_1(C_321)) = k5_relat_1('#skF_3',k2_funct_1(C_321))
      | ~ v1_funct_1(k2_funct_1(C_321))
      | k2_relset_1(A_320,B_319,C_321) != B_319
      | ~ v2_funct_1(C_321)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_320,B_319)))
      | ~ v1_funct_2(C_321,A_320,B_319)
      | ~ v1_funct_1(C_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2246])).

tff(c_2257,plain,
    ( k1_partfun1(k2_struct_0('#skF_1'),'#skF_3','#skF_3',k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1921,c_2251])).

tff(c_2261,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),'#skF_3','#skF_3',k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1925,c_46,c_1924,c_1962,c_2257])).

tff(c_2003,plain,(
    ! [A_261,B_262,C_263] :
      ( k2_tops_2(A_261,B_262,C_263) = k2_funct_1(C_263)
      | ~ v2_funct_1(C_263)
      | k2_relset_1(A_261,B_262,C_263) != B_262
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_2(C_263,A_261,B_262)
      | ~ v1_funct_1(C_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2006,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1921,c_2003])).

tff(c_2009,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1925,c_1924,c_46,c_2006])).

tff(c_1927,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1919,c_1792])).

tff(c_1966,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),'#skF_3','#skF_3',k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_1927,c_1927,c_130])).

tff(c_2010,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),'#skF_3','#skF_3',k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2009,c_1966])).

tff(c_2262,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2261,c_2010])).

tff(c_2269,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2262])).

tff(c_2273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_2269])).

tff(c_2274,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_2305,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2304,c_2304,c_2304,c_2274])).

tff(c_2376,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2375,c_2305])).

tff(c_2478,plain,(
    k1_partfun1(k1_xboole_0,k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),k1_xboole_0,k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2474,c_2474,c_2474,c_2376])).

tff(c_2713,plain,(
    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2581,c_2581,c_2478])).

tff(c_2798,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2792,c_2713])).

tff(c_2805,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1(k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_2798])).

tff(c_2808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_2773,c_2805])).

tff(c_2809,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2566])).

tff(c_2816,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2484])).

tff(c_2817,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2809,c_2483])).

tff(c_2815,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2480])).

tff(c_2812,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2482])).

tff(c_2855,plain,
    ( k1_relset_1('#skF_3',k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2812,c_2452])).

tff(c_2878,plain,(
    k1_relset_1('#skF_3',k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2816,c_46,c_2817,c_2855])).

tff(c_2449,plain,(
    ! [A_356,C_354] :
      ( k1_relset_1(k1_xboole_0,A_356,k2_funct_1(C_354)) = k1_xboole_0
      | ~ v1_funct_2(k2_funct_1(C_354),k1_xboole_0,A_356)
      | k2_relset_1(A_356,k1_xboole_0,C_354) != k1_xboole_0
      | ~ v2_funct_1(C_354)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_356,k1_xboole_0)))
      | ~ v1_funct_2(C_354,A_356,k1_xboole_0)
      | ~ v1_funct_1(C_354) ) ),
    inference(resolution,[status(thm)],[c_2403,c_22])).

tff(c_2971,plain,(
    ! [A_394,C_395] :
      ( k1_relset_1('#skF_3',A_394,k2_funct_1(C_395)) = '#skF_3'
      | ~ v1_funct_2(k2_funct_1(C_395),'#skF_3',A_394)
      | k2_relset_1(A_394,'#skF_3',C_395) != '#skF_3'
      | ~ v2_funct_1(C_395)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(A_394,'#skF_3')))
      | ~ v1_funct_2(C_395,A_394,'#skF_3')
      | ~ v1_funct_1(C_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2809,c_2809,c_2809,c_2809,c_2809,c_2809,c_2449])).

tff(c_2974,plain,
    ( k1_relset_1('#skF_3',k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2812,c_2971])).

tff(c_2981,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2816,c_46,c_2817,c_2815,c_2878,c_2974])).

tff(c_2987,plain,
    ( k2_relat_1('#skF_3') = '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2981,c_4])).

tff(c_2994,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_2987])).

tff(c_2819,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2474])).

tff(c_3066,plain,(
    ! [B_411,A_412,C_413] :
      ( k1_partfun1(B_411,A_412,k1_relat_1('#skF_3'),'#skF_3',k2_funct_1(C_413),'#skF_3') = k5_relat_1(k2_funct_1(C_413),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_413))
      | k2_relset_1(A_412,B_411,C_413) != B_411
      | ~ v2_funct_1(C_413)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_412,B_411)))
      | ~ v1_funct_2(C_413,A_412,B_411)
      | ~ v1_funct_1(C_413) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_2442])).

tff(c_3069,plain,
    ( k1_partfun1('#skF_3',k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2812,c_3066])).

tff(c_3075,plain,(
    k1_partfun1('#skF_3',k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2816,c_46,c_2817,c_2361,c_3069])).

tff(c_2914,plain,(
    k1_partfun1('#skF_3',k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2809,c_2809,c_2478])).

tff(c_3077,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3075,c_2914])).

tff(c_3084,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_3077])).

tff(c_3087,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_2994,c_3084])).

tff(c_3089,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2473])).

tff(c_3106,plain,(
    ! [B_414,C_415,A_416] :
      ( k6_partfun1(B_414) = k5_relat_1(k2_funct_1(C_415),C_415)
      | k1_xboole_0 = B_414
      | ~ v2_funct_1(C_415)
      | k2_relset_1(A_416,B_414,C_415) != B_414
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_416,B_414)))
      | ~ v1_funct_2(C_415,A_416,B_414)
      | ~ v1_funct_1(C_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3110,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2307,c_3106])).

tff(c_3114,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2308,c_2309,c_46,c_3110])).

tff(c_3115,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_3089,c_3114])).

tff(c_3130,plain,
    ( k6_partfun1(k2_struct_0('#skF_2')) = k6_partfun1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3115,c_61])).

tff(c_3137,plain,(
    k6_partfun1(k2_struct_0('#skF_2')) = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_3130])).

tff(c_3141,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3137,c_3115])).

tff(c_3395,plain,(
    ! [B_442,A_443,C_444] :
      ( k1_partfun1(B_442,A_443,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(C_444),'#skF_3') = k5_relat_1(k2_funct_1(C_444),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_444))
      | k2_relset_1(A_443,B_442,C_444) != B_442
      | ~ v2_funct_1(C_444)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_443,B_442)))
      | ~ v1_funct_2(C_444,A_443,B_442)
      | ~ v1_funct_1(C_444) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3214,c_2442])).

tff(c_3142,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3137,c_2376])).

tff(c_3219,plain,(
    k1_partfun1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3214,c_3214,c_3142])).

tff(c_3401,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3395,c_3219])).

tff(c_3408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3230,c_3228,c_46,c_3229,c_2361,c_3141,c_3401])).

tff(c_3409,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3190])).

tff(c_3422,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3409,c_2308])).

tff(c_3421,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3409,c_2309])).

tff(c_3418,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3409,c_2368])).

tff(c_3420,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3409,c_2307])).

tff(c_2451,plain,(
    ! [C_354,B_355] :
      ( k2_funct_1(C_354) = k1_xboole_0
      | ~ v1_funct_2(k2_funct_1(C_354),B_355,k1_xboole_0)
      | k1_xboole_0 = B_355
      | k2_relset_1(k1_xboole_0,B_355,C_354) != B_355
      | ~ v2_funct_1(C_354)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_355)))
      | ~ v1_funct_2(C_354,k1_xboole_0,B_355)
      | ~ v1_funct_1(C_354) ) ),
    inference(resolution,[status(thm)],[c_2403,c_16])).

tff(c_3451,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_xboole_0)
    | k2_struct_0('#skF_2') = k1_xboole_0
    | k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3420,c_2451])).

tff(c_3500,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_xboole_0)
    | k2_struct_0('#skF_2') = k1_xboole_0
    | k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_3451])).

tff(c_3501,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_xboole_0)
    | k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_3089,c_3500])).

tff(c_3638,plain,(
    k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3422,c_3421,c_3418,c_3501])).

tff(c_3665,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1(k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3638,c_4])).

tff(c_3680,plain,(
    k2_relat_1('#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_3665])).

tff(c_3647,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k5_relat_1(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3638,c_3141])).

tff(c_3714,plain,(
    k6_partfun1(k1_relat_1(k1_xboole_0)) = k5_relat_1(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3680,c_3647])).

tff(c_3411,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k1_xboole_0,k1_xboole_0,k2_struct_0('#skF_2'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3409,c_3409,c_3142])).

tff(c_3640,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k1_xboole_0,k1_xboole_0,k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3638,c_3411])).

tff(c_3744,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k1_xboole_0,k1_xboole_0,k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3') != k5_relat_1(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3714,c_3680,c_3640])).

tff(c_3649,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3638,c_2361])).

tff(c_30,plain,(
    ! [C_21,B_20,A_19] :
      ( m1_subset_1(k2_funct_1(C_21),k1_zfmisc_1(k2_zfmisc_1(B_20,A_19)))
      | k2_relset_1(A_19,B_20,C_21) != B_20
      | ~ v2_funct_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3656,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(B_20,A_19)))
      | k2_relset_1(A_19,B_20,'#skF_3') != B_20
      | ~ v2_funct_1('#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2('#skF_3',A_19,B_20)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3638,c_30])).

tff(c_3745,plain,(
    ! [B_469,A_470] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(B_469,A_470)))
      | k2_relset_1(A_470,B_469,'#skF_3') != B_469
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_470,B_469)))
      | ~ v1_funct_2('#skF_3',A_470,B_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_3656])).

tff(c_3415,plain,(
    ! [A_346,B_345,E_347] :
      ( k1_partfun1(A_346,B_345,k1_xboole_0,k2_struct_0('#skF_2'),E_347,'#skF_3') = k5_relat_1(E_347,'#skF_3')
      | ~ m1_subset_1(E_347,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345)))
      | ~ v1_funct_1(E_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3409,c_2391])).

tff(c_3755,plain,(
    ! [B_469,A_470] :
      ( k1_partfun1(B_469,A_470,k1_xboole_0,k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3') = k5_relat_1(k1_xboole_0,'#skF_3')
      | ~ v1_funct_1(k1_xboole_0)
      | k2_relset_1(A_470,B_469,'#skF_3') != B_469
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_470,B_469)))
      | ~ v1_funct_2('#skF_3',A_470,B_469) ) ),
    inference(resolution,[status(thm)],[c_3745,c_3415])).

tff(c_3955,plain,(
    ! [B_486,A_487] :
      ( k1_partfun1(B_486,A_487,k1_xboole_0,k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3') = k5_relat_1(k1_xboole_0,'#skF_3')
      | k2_relset_1(A_487,B_486,'#skF_3') != B_486
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_487,B_486)))
      | ~ v1_funct_2('#skF_3',A_487,B_486) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3649,c_3755])).

tff(c_3958,plain,
    ( k1_partfun1(k2_struct_0('#skF_2'),k1_xboole_0,k1_xboole_0,k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3') = k5_relat_1(k1_xboole_0,'#skF_3')
    | k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3420,c_3955])).

tff(c_3961,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k1_xboole_0,k1_xboole_0,k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3') = k5_relat_1(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3422,c_3421,c_3958])).

tff(c_3963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3744,c_3961])).

tff(c_3964,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2303])).

tff(c_3968,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3964,c_94])).

tff(c_3967,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3964,c_95])).

tff(c_3988,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3967,c_16])).

tff(c_4001,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3968,c_3988])).

tff(c_4005,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4001])).

tff(c_3965,plain,(
    k2_struct_0('#skF_1') != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2303])).

tff(c_4008,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4005,c_3965])).

tff(c_4007,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4005,c_3968])).

tff(c_4006,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4005,c_3967])).

tff(c_4032,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4006,c_22])).

tff(c_4054,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4007,c_4032])).

tff(c_4061,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4006,c_12])).

tff(c_4068,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_4061])).

tff(c_4069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4008,c_4068])).

tff(c_4070,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4001])).

tff(c_4073,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4070,c_3968])).

tff(c_3969,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3964,c_3964,c_89])).

tff(c_4074,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4070,c_4070,c_3969])).

tff(c_4072,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4070,c_3967])).

tff(c_4162,plain,(
    ! [C_507,B_508,A_509] :
      ( v1_funct_2(k2_funct_1(C_507),B_508,A_509)
      | k2_relset_1(A_509,B_508,C_507) != B_508
      | ~ v2_funct_1(C_507)
      | ~ m1_subset_1(C_507,k1_zfmisc_1(k2_zfmisc_1(A_509,B_508)))
      | ~ v1_funct_2(C_507,A_509,B_508)
      | ~ v1_funct_1(C_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4165,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4072,c_4162])).

tff(c_4168,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4073,c_46,c_4074,c_4165])).

tff(c_4176,plain,(
    ! [C_513,B_514,A_515] :
      ( m1_subset_1(k2_funct_1(C_513),k1_zfmisc_1(k2_zfmisc_1(B_514,A_515)))
      | k2_relset_1(A_515,B_514,C_513) != B_514
      | ~ v2_funct_1(C_513)
      | ~ m1_subset_1(C_513,k1_zfmisc_1(k2_zfmisc_1(A_515,B_514)))
      | ~ v1_funct_2(C_513,A_515,B_514)
      | ~ v1_funct_1(C_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4287,plain,(
    ! [B_534,A_535,C_536] :
      ( k1_relset_1(B_534,A_535,k2_funct_1(C_536)) = k1_relat_1(k2_funct_1(C_536))
      | k2_relset_1(A_535,B_534,C_536) != B_534
      | ~ v2_funct_1(C_536)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(A_535,B_534)))
      | ~ v1_funct_2(C_536,A_535,B_534)
      | ~ v1_funct_1(C_536) ) ),
    inference(resolution,[status(thm)],[c_4176,c_12])).

tff(c_4293,plain,
    ( k1_relset_1('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4072,c_4287])).

tff(c_4297,plain,(
    k1_relset_1('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4073,c_46,c_4074,c_4293])).

tff(c_4078,plain,(
    ! [B_10,C_11] :
      ( k1_relset_1('#skF_3',B_10,C_11) = '#skF_3'
      | ~ v1_funct_2(C_11,'#skF_3',B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_10))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4070,c_4070,c_4070,c_4070,c_22])).

tff(c_4329,plain,(
    ! [A_542,C_543] :
      ( k1_relset_1('#skF_3',A_542,k2_funct_1(C_543)) = '#skF_3'
      | ~ v1_funct_2(k2_funct_1(C_543),'#skF_3',A_542)
      | k2_relset_1(A_542,'#skF_3',C_543) != '#skF_3'
      | ~ v2_funct_1(C_543)
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_542,'#skF_3')))
      | ~ v1_funct_2(C_543,A_542,'#skF_3')
      | ~ v1_funct_1(C_543) ) ),
    inference(resolution,[status(thm)],[c_4176,c_4078])).

tff(c_4336,plain,
    ( k1_relset_1('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4072,c_4329])).

tff(c_4340,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4073,c_46,c_4074,c_4168,c_4297,c_4336])).

tff(c_4345,plain,
    ( k2_relat_1('#skF_3') = '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4340,c_4])).

tff(c_4352,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_4345])).

tff(c_4138,plain,(
    ! [C_497,A_498,B_499] :
      ( v1_funct_1(k2_funct_1(C_497))
      | k2_relset_1(A_498,B_499,C_497) != B_499
      | ~ v2_funct_1(C_497)
      | ~ m1_subset_1(C_497,k1_zfmisc_1(k2_zfmisc_1(A_498,B_499)))
      | ~ v1_funct_2(C_497,A_498,B_499)
      | ~ v1_funct_1(C_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4141,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4072,c_4138])).

tff(c_4144,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4073,c_46,c_4074,c_4141])).

tff(c_4230,plain,(
    ! [A_517,F_520,B_516,C_521,D_519,E_518] :
      ( k1_partfun1(A_517,B_516,C_521,D_519,E_518,F_520) = k5_relat_1(E_518,F_520)
      | ~ m1_subset_1(F_520,k1_zfmisc_1(k2_zfmisc_1(C_521,D_519)))
      | ~ v1_funct_1(F_520)
      | ~ m1_subset_1(E_518,k1_zfmisc_1(k2_zfmisc_1(A_517,B_516)))
      | ~ v1_funct_1(E_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4234,plain,(
    ! [A_517,B_516,E_518] :
      ( k1_partfun1(A_517,B_516,k2_struct_0('#skF_1'),'#skF_3',E_518,'#skF_3') = k5_relat_1(E_518,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_518,k1_zfmisc_1(k2_zfmisc_1(A_517,B_516)))
      | ~ v1_funct_1(E_518) ) ),
    inference(resolution,[status(thm)],[c_4072,c_4230])).

tff(c_4239,plain,(
    ! [A_522,B_523,E_524] :
      ( k1_partfun1(A_522,B_523,k2_struct_0('#skF_1'),'#skF_3',E_524,'#skF_3') = k5_relat_1(E_524,'#skF_3')
      | ~ m1_subset_1(E_524,k1_zfmisc_1(k2_zfmisc_1(A_522,B_523)))
      | ~ v1_funct_1(E_524) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4234])).

tff(c_4308,plain,(
    ! [B_539,A_540,C_541] :
      ( k1_partfun1(B_539,A_540,k2_struct_0('#skF_1'),'#skF_3',k2_funct_1(C_541),'#skF_3') = k5_relat_1(k2_funct_1(C_541),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_541))
      | k2_relset_1(A_540,B_539,C_541) != B_539
      | ~ v2_funct_1(C_541)
      | ~ m1_subset_1(C_541,k1_zfmisc_1(k2_zfmisc_1(A_540,B_539)))
      | ~ v1_funct_2(C_541,A_540,B_539)
      | ~ v1_funct_1(C_541) ) ),
    inference(resolution,[status(thm)],[c_30,c_4239])).

tff(c_4314,plain,
    ( k1_partfun1('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4072,c_4308])).

tff(c_4318,plain,(
    k1_partfun1('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4073,c_46,c_4074,c_4144,c_4314])).

tff(c_4169,plain,(
    ! [A_510,B_511,C_512] :
      ( k2_tops_2(A_510,B_511,C_512) = k2_funct_1(C_512)
      | ~ v2_funct_1(C_512)
      | k2_relset_1(A_510,B_511,C_512) != B_511
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(A_510,B_511)))
      | ~ v1_funct_2(C_512,A_510,B_511)
      | ~ v1_funct_1(C_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4172,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4072,c_4169])).

tff(c_4175,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4073,c_4074,c_46,c_4172])).

tff(c_4076,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4070,c_3964])).

tff(c_4161,plain,(
    k1_partfun1('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3'),'#skF_3') != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4076,c_4076,c_4076,c_4076,c_2274])).

tff(c_4220,plain,(
    k1_partfun1('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4175,c_4161])).

tff(c_4319,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4318,c_4220])).

tff(c_4326,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4319])).

tff(c_4328,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_46,c_4326])).

tff(c_4369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4352,c_4328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.78/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.84/2.40  
% 6.84/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.84/2.41  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_partfun1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.84/2.41  
% 6.84/2.41  %Foreground sorts:
% 6.84/2.41  
% 6.84/2.41  
% 6.84/2.41  %Background operators:
% 6.84/2.41  
% 6.84/2.41  
% 6.84/2.41  %Foreground operators:
% 6.84/2.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.84/2.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.84/2.41  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.84/2.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.84/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.84/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.84/2.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.84/2.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.84/2.41  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 6.84/2.41  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.84/2.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.84/2.41  tff('#skF_2', type, '#skF_2': $i).
% 6.84/2.41  tff('#skF_3', type, '#skF_3': $i).
% 6.84/2.41  tff('#skF_1', type, '#skF_1': $i).
% 6.84/2.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.84/2.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.84/2.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.84/2.41  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.84/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.84/2.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.84/2.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.84/2.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.84/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.84/2.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.84/2.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.84/2.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.84/2.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.84/2.41  
% 7.06/2.45  tff(f_152, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_partfun1(u1_struct_0(A), u1_struct_0(B), u1_struct_0(B), u1_struct_0(A), C, k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k6_partfun1(k1_relset_1(u1_struct_0(A), u1_struct_0(B), C))) & (k1_partfun1(u1_struct_0(B), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), C) = k6_partfun1(k2_relset_1(u1_struct_0(A), u1_struct_0(B), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_2)).
% 7.06/2.45  tff(f_119, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.06/2.45  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.06/2.45  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.06/2.45  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.06/2.45  tff(f_99, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 7.06/2.45  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.06/2.45  tff(f_115, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.06/2.45  tff(f_83, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.06/2.45  tff(f_45, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.06/2.45  tff(f_81, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.06/2.45  tff(f_131, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 7.06/2.45  tff(c_58, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.06/2.45  tff(c_71, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.06/2.45  tff(c_79, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_71])).
% 7.06/2.45  tff(c_56, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.06/2.45  tff(c_78, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_71])).
% 7.06/2.45  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.06/2.45  tff(c_95, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_78, c_50])).
% 7.06/2.45  tff(c_96, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.06/2.45  tff(c_100, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_95, c_96])).
% 7.06/2.45  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.06/2.45  tff(c_46, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.06/2.45  tff(c_52, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.06/2.45  tff(c_80, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_52])).
% 7.06/2.45  tff(c_94, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_80])).
% 7.06/2.45  tff(c_119, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.06/2.45  tff(c_123, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_95, c_119])).
% 7.06/2.45  tff(c_2297, plain, (![B_330, A_331, C_332]: (k1_xboole_0=B_330 | k1_relset_1(A_331, B_330, C_332)=A_331 | ~v1_funct_2(C_332, A_331, B_330) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_331, B_330))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.06/2.45  tff(c_2300, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_95, c_2297])).
% 7.06/2.45  tff(c_2303, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_123, c_2300])).
% 7.06/2.45  tff(c_2304, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_2303])).
% 7.06/2.45  tff(c_2308, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2304, c_94])).
% 7.06/2.45  tff(c_48, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.06/2.45  tff(c_89, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_78, c_48])).
% 7.06/2.45  tff(c_2309, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2304, c_89])).
% 7.06/2.45  tff(c_2307, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2304, c_95])).
% 7.06/2.45  tff(c_2362, plain, (![C_339, B_340, A_341]: (v1_funct_2(k2_funct_1(C_339), B_340, A_341) | k2_relset_1(A_341, B_340, C_339)!=B_340 | ~v2_funct_1(C_339) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_341, B_340))) | ~v1_funct_2(C_339, A_341, B_340) | ~v1_funct_1(C_339))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.06/2.45  tff(c_2365, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2307, c_2362])).
% 7.06/2.45  tff(c_2368, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2308, c_46, c_2309, c_2365])).
% 7.06/2.45  tff(c_2403, plain, (![C_354, B_355, A_356]: (m1_subset_1(k2_funct_1(C_354), k1_zfmisc_1(k2_zfmisc_1(B_355, A_356))) | k2_relset_1(A_356, B_355, C_354)!=B_355 | ~v2_funct_1(C_354) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_356, B_355))) | ~v1_funct_2(C_354, A_356, B_355) | ~v1_funct_1(C_354))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.06/2.45  tff(c_12, plain, (![A_6, B_7, C_8]: (k1_relset_1(A_6, B_7, C_8)=k1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.06/2.45  tff(c_3116, plain, (![B_417, A_418, C_419]: (k1_relset_1(B_417, A_418, k2_funct_1(C_419))=k1_relat_1(k2_funct_1(C_419)) | k2_relset_1(A_418, B_417, C_419)!=B_417 | ~v2_funct_1(C_419) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(A_418, B_417))) | ~v1_funct_2(C_419, A_418, B_417) | ~v1_funct_1(C_419))), inference(resolution, [status(thm)], [c_2403, c_12])).
% 7.06/2.45  tff(c_3122, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2307, c_3116])).
% 7.06/2.45  tff(c_3126, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2308, c_46, c_2309, c_3122])).
% 7.06/2.45  tff(c_24, plain, (![B_10, A_9, C_11]: (k1_xboole_0=B_10 | k1_relset_1(A_9, B_10, C_11)=A_9 | ~v1_funct_2(C_11, A_9, B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.06/2.45  tff(c_3180, plain, (![A_424, B_425, C_426]: (k1_xboole_0=A_424 | k1_relset_1(B_425, A_424, k2_funct_1(C_426))=B_425 | ~v1_funct_2(k2_funct_1(C_426), B_425, A_424) | k2_relset_1(A_424, B_425, C_426)!=B_425 | ~v2_funct_1(C_426) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(A_424, B_425))) | ~v1_funct_2(C_426, A_424, B_425) | ~v1_funct_1(C_426))), inference(resolution, [status(thm)], [c_2403, c_24])).
% 7.06/2.45  tff(c_3186, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2307, c_3180])).
% 7.06/2.45  tff(c_3190, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1(k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2308, c_46, c_2309, c_2368, c_3126, c_3186])).
% 7.06/2.45  tff(c_3202, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3190])).
% 7.06/2.45  tff(c_4, plain, (![A_1]: (k1_relat_1(k2_funct_1(A_1))=k2_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.06/2.45  tff(c_3207, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3202, c_4])).
% 7.06/2.45  tff(c_3214, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_3207])).
% 7.06/2.45  tff(c_3230, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3214, c_2308])).
% 7.06/2.45  tff(c_3228, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_3214, c_2307])).
% 7.06/2.45  tff(c_3229, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3214, c_3214, c_2309])).
% 7.06/2.45  tff(c_2355, plain, (![C_336, A_337, B_338]: (v1_funct_1(k2_funct_1(C_336)) | k2_relset_1(A_337, B_338, C_336)!=B_338 | ~v2_funct_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))) | ~v1_funct_2(C_336, A_337, B_338) | ~v1_funct_1(C_336))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.06/2.45  tff(c_2358, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2307, c_2355])).
% 7.06/2.45  tff(c_2361, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2308, c_46, c_2309, c_2358])).
% 7.06/2.45  tff(c_2465, plain, (![A_360, C_361, B_362]: (k6_partfun1(A_360)=k5_relat_1(C_361, k2_funct_1(C_361)) | k1_xboole_0=B_362 | ~v2_funct_1(C_361) | k2_relset_1(A_360, B_362, C_361)!=B_362 | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_360, B_362))) | ~v1_funct_2(C_361, A_360, B_362) | ~v1_funct_1(C_361))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.06/2.45  tff(c_2469, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k2_struct_0('#skF_2')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2307, c_2465])).
% 7.06/2.45  tff(c_2473, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2308, c_2309, c_46, c_2469])).
% 7.06/2.45  tff(c_2474, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2473])).
% 7.06/2.45  tff(c_2484, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2474, c_2308])).
% 7.06/2.45  tff(c_2482, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2474, c_2307])).
% 7.06/2.45  tff(c_16, plain, (![C_11, A_9]: (k1_xboole_0=C_11 | ~v1_funct_2(C_11, A_9, k1_xboole_0) | k1_xboole_0=A_9 | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.06/2.45  tff(c_2530, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0) | k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2482, c_16])).
% 7.06/2.45  tff(c_2566, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2484, c_2530])).
% 7.06/2.45  tff(c_2581, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2566])).
% 7.06/2.45  tff(c_2586, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2581, c_2484])).
% 7.06/2.45  tff(c_2483, plain, (k2_relset_1(k1_relat_1('#skF_3'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2474, c_2474, c_2309])).
% 7.06/2.45  tff(c_2587, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2581, c_2483])).
% 7.06/2.45  tff(c_2480, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_xboole_0, k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2474, c_2368])).
% 7.06/2.45  tff(c_2585, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2581, c_2480])).
% 7.06/2.45  tff(c_2582, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2581, c_2482])).
% 7.06/2.45  tff(c_2452, plain, (![B_355, A_356, C_354]: (k1_relset_1(B_355, A_356, k2_funct_1(C_354))=k1_relat_1(k2_funct_1(C_354)) | k2_relset_1(A_356, B_355, C_354)!=B_355 | ~v2_funct_1(C_354) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_356, B_355))) | ~v1_funct_2(C_354, A_356, B_355) | ~v1_funct_1(C_354))), inference(resolution, [status(thm)], [c_2403, c_12])).
% 7.06/2.45  tff(c_2621, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2582, c_2452])).
% 7.06/2.45  tff(c_2663, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2586, c_46, c_2587, c_2621])).
% 7.06/2.45  tff(c_22, plain, (![B_10, C_11]: (k1_relset_1(k1_xboole_0, B_10, C_11)=k1_xboole_0 | ~v1_funct_2(C_11, k1_xboole_0, B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_10))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.06/2.45  tff(c_2750, plain, (![A_374, C_375]: (k1_relset_1(k1_xboole_0, A_374, k2_funct_1(C_375))=k1_xboole_0 | ~v1_funct_2(k2_funct_1(C_375), k1_xboole_0, A_374) | k2_relset_1(A_374, k1_xboole_0, C_375)!=k1_xboole_0 | ~v2_funct_1(C_375) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_374, k1_xboole_0))) | ~v1_funct_2(C_375, A_374, k1_xboole_0) | ~v1_funct_1(C_375))), inference(resolution, [status(thm)], [c_2403, c_22])).
% 7.06/2.45  tff(c_2753, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_3'), k1_xboole_0, k1_xboole_0) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2582, c_2750])).
% 7.06/2.45  tff(c_2760, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2586, c_46, c_2587, c_2585, c_2663, c_2753])).
% 7.06/2.45  tff(c_2766, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2760, c_4])).
% 7.06/2.45  tff(c_2773, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_2766])).
% 7.06/2.45  tff(c_28, plain, (![A_18]: (k6_relat_1(A_18)=k6_partfun1(A_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.06/2.45  tff(c_6, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.06/2.45  tff(c_61, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_partfun1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6])).
% 7.06/2.45  tff(c_2386, plain, (![B_345, C_350, D_348, A_346, E_347, F_349]: (k1_partfun1(A_346, B_345, C_350, D_348, E_347, F_349)=k5_relat_1(E_347, F_349) | ~m1_subset_1(F_349, k1_zfmisc_1(k2_zfmisc_1(C_350, D_348))) | ~v1_funct_1(F_349) | ~m1_subset_1(E_347, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))) | ~v1_funct_1(E_347))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.06/2.45  tff(c_2388, plain, (![A_346, B_345, E_347]: (k1_partfun1(A_346, B_345, k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), E_347, '#skF_3')=k5_relat_1(E_347, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_347, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))) | ~v1_funct_1(E_347))), inference(resolution, [status(thm)], [c_2307, c_2386])).
% 7.06/2.45  tff(c_2391, plain, (![A_346, B_345, E_347]: (k1_partfun1(A_346, B_345, k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), E_347, '#skF_3')=k5_relat_1(E_347, '#skF_3') | ~m1_subset_1(E_347, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))) | ~v1_funct_1(E_347))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2388])).
% 7.06/2.45  tff(c_2442, plain, (![B_355, A_356, C_354]: (k1_partfun1(B_355, A_356, k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_funct_1(C_354), '#skF_3')=k5_relat_1(k2_funct_1(C_354), '#skF_3') | ~v1_funct_1(k2_funct_1(C_354)) | k2_relset_1(A_356, B_355, C_354)!=B_355 | ~v2_funct_1(C_354) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_356, B_355))) | ~v1_funct_2(C_354, A_356, B_355) | ~v1_funct_1(C_354))), inference(resolution, [status(thm)], [c_2403, c_2391])).
% 7.06/2.45  tff(c_2783, plain, (![B_376, A_377, C_378]: (k1_partfun1(B_376, A_377, k1_xboole_0, k1_xboole_0, k2_funct_1(C_378), '#skF_3')=k5_relat_1(k2_funct_1(C_378), '#skF_3') | ~v1_funct_1(k2_funct_1(C_378)) | k2_relset_1(A_377, B_376, C_378)!=B_376 | ~v2_funct_1(C_378) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(A_377, B_376))) | ~v1_funct_2(C_378, A_377, B_376) | ~v1_funct_1(C_378))), inference(demodulation, [status(thm), theory('equality')], [c_2581, c_2474, c_2442])).
% 7.06/2.45  tff(c_2786, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2582, c_2783])).
% 7.06/2.45  tff(c_2792, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2586, c_46, c_2587, c_2361, c_2786])).
% 7.06/2.45  tff(c_2369, plain, (![A_342, B_343, C_344]: (k2_tops_2(A_342, B_343, C_344)=k2_funct_1(C_344) | ~v2_funct_1(C_344) | k2_relset_1(A_342, B_343, C_344)!=B_343 | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))) | ~v1_funct_2(C_344, A_342, B_343) | ~v1_funct_1(C_344))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.06/2.45  tff(c_2372, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2307, c_2369])).
% 7.06/2.45  tff(c_2375, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2308, c_2309, c_46, c_2372])).
% 7.06/2.45  tff(c_8, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_relat_1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.06/2.45  tff(c_60, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_partfun1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8])).
% 7.06/2.45  tff(c_152, plain, (![B_52, A_53, C_54]: (k1_xboole_0=B_52 | k1_relset_1(A_53, B_52, C_54)=A_53 | ~v1_funct_2(C_54, A_53, B_52) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.06/2.45  tff(c_155, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_95, c_152])).
% 7.06/2.45  tff(c_158, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_123, c_155])).
% 7.06/2.45  tff(c_159, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_158])).
% 7.06/2.45  tff(c_162, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_94])).
% 7.06/2.45  tff(c_163, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_89])).
% 7.06/2.45  tff(c_161, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_95])).
% 7.06/2.45  tff(c_310, plain, (![B_82, C_83, A_84]: (k6_partfun1(B_82)=k5_relat_1(k2_funct_1(C_83), C_83) | k1_xboole_0=B_82 | ~v2_funct_1(C_83) | k2_relset_1(A_84, B_82, C_83)!=B_82 | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_82))) | ~v1_funct_2(C_83, A_84, B_82) | ~v1_funct_1(C_83))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.06/2.45  tff(c_314, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_161, c_310])).
% 7.06/2.45  tff(c_318, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_162, c_163, c_46, c_314])).
% 7.06/2.45  tff(c_319, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_318])).
% 7.06/2.45  tff(c_327, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_319, c_162])).
% 7.06/2.45  tff(c_328, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_161])).
% 7.06/2.45  tff(c_372, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0) | k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_328, c_16])).
% 7.06/2.45  tff(c_411, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_327, c_372])).
% 7.06/2.45  tff(c_419, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_411])).
% 7.06/2.45  tff(c_424, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_419, c_327])).
% 7.06/2.45  tff(c_326, plain, (k2_relset_1(k1_relat_1('#skF_3'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_319, c_319, c_163])).
% 7.06/2.45  tff(c_422, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_419, c_326])).
% 7.06/2.45  tff(c_202, plain, (![C_58, A_59, B_60]: (v1_funct_1(k2_funct_1(C_58)) | k2_relset_1(A_59, B_60, C_58)!=B_60 | ~v2_funct_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_2(C_58, A_59, B_60) | ~v1_funct_1(C_58))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.06/2.45  tff(c_205, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_161, c_202])).
% 7.06/2.45  tff(c_208, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_162, c_46, c_163, c_205])).
% 7.06/2.45  tff(c_421, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_419, c_328])).
% 7.06/2.45  tff(c_237, plain, (![C_73, B_74, A_75]: (m1_subset_1(k2_funct_1(C_73), k1_zfmisc_1(k2_zfmisc_1(B_74, A_75))) | k2_relset_1(A_75, B_74, C_73)!=B_74 | ~v2_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))) | ~v1_funct_2(C_73, A_75, B_74) | ~v1_funct_1(C_73))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.06/2.45  tff(c_26, plain, (![E_16, D_15, F_17, C_14, A_12, B_13]: (k1_partfun1(A_12, B_13, C_14, D_15, E_16, F_17)=k5_relat_1(E_16, F_17) | ~m1_subset_1(F_17, k1_zfmisc_1(k2_zfmisc_1(C_14, D_15))) | ~v1_funct_1(F_17) | ~m1_subset_1(E_16, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_funct_1(E_16))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.06/2.45  tff(c_673, plain, (![E_115, A_116, B_113, A_114, C_118, B_117]: (k1_partfun1(A_114, B_113, B_117, A_116, E_115, k2_funct_1(C_118))=k5_relat_1(E_115, k2_funct_1(C_118)) | ~v1_funct_1(k2_funct_1(C_118)) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))) | ~v1_funct_1(E_115) | k2_relset_1(A_116, B_117, C_118)!=B_117 | ~v2_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_2(C_118, A_116, B_117) | ~v1_funct_1(C_118))), inference(resolution, [status(thm)], [c_237, c_26])).
% 7.06/2.45  tff(c_675, plain, (![B_117, A_116, C_118]: (k1_partfun1(k1_xboole_0, k1_xboole_0, B_117, A_116, '#skF_3', k2_funct_1(C_118))=k5_relat_1('#skF_3', k2_funct_1(C_118)) | ~v1_funct_1(k2_funct_1(C_118)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_116, B_117, C_118)!=B_117 | ~v2_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_2(C_118, A_116, B_117) | ~v1_funct_1(C_118))), inference(resolution, [status(thm)], [c_421, c_673])).
% 7.06/2.45  tff(c_682, plain, (![B_119, A_120, C_121]: (k1_partfun1(k1_xboole_0, k1_xboole_0, B_119, A_120, '#skF_3', k2_funct_1(C_121))=k5_relat_1('#skF_3', k2_funct_1(C_121)) | ~v1_funct_1(k2_funct_1(C_121)) | k2_relset_1(A_120, B_119, C_121)!=B_119 | ~v2_funct_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(C_121, A_120, B_119) | ~v1_funct_1(C_121))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_675])).
% 7.06/2.45  tff(c_685, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_421, c_682])).
% 7.06/2.45  tff(c_691, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_424, c_46, c_422, c_208, c_685])).
% 7.06/2.45  tff(c_219, plain, (![A_64, B_65, C_66]: (k2_tops_2(A_64, B_65, C_66)=k2_funct_1(C_66) | ~v2_funct_1(C_66) | k2_relset_1(A_64, B_65, C_66)!=B_65 | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_2(C_66, A_64, B_65) | ~v1_funct_1(C_66))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.06/2.45  tff(c_222, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_161, c_219])).
% 7.06/2.45  tff(c_225, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_162, c_163, c_46, c_222])).
% 7.06/2.45  tff(c_44, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.06/2.45  tff(c_59, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44])).
% 7.24/2.45  tff(c_129, plain, (k1_partfun1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2')) | k1_partfun1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_79, c_79, c_79, c_79, c_78, c_78, c_78, c_78, c_79, c_79, c_79, c_78, c_78, c_78, c_59])).
% 7.24/2.45  tff(c_130, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_129])).
% 7.24/2.45  tff(c_211, plain, (k1_partfun1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), '#skF_3', k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_159, c_159, c_130])).
% 7.24/2.45  tff(c_226, plain, (k1_partfun1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_211])).
% 7.24/2.45  tff(c_322, plain, (k1_partfun1(k1_relat_1('#skF_3'), k1_xboole_0, k1_xboole_0, k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_319, c_226])).
% 7.24/2.45  tff(c_571, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_419, c_419, c_419, c_322])).
% 7.24/2.45  tff(c_693, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_691, c_571])).
% 7.24/2.45  tff(c_700, plain, (k6_partfun1(k1_relat_1('#skF_3'))!=k6_partfun1(k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_60, c_693])).
% 7.24/2.45  tff(c_703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_419, c_700])).
% 7.24/2.45  tff(c_704, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_411])).
% 7.24/2.45  tff(c_712, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_704, c_327])).
% 7.24/2.45  tff(c_709, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_704, c_704, c_326])).
% 7.24/2.45  tff(c_708, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_704, c_328])).
% 7.24/2.45  tff(c_1005, plain, (![A_170, A_172, C_174, E_171, B_173, B_169]: (k1_partfun1(A_170, B_169, B_173, A_172, E_171, k2_funct_1(C_174))=k5_relat_1(E_171, k2_funct_1(C_174)) | ~v1_funct_1(k2_funct_1(C_174)) | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))) | ~v1_funct_1(E_171) | k2_relset_1(A_172, B_173, C_174)!=B_173 | ~v2_funct_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_2(C_174, A_172, B_173) | ~v1_funct_1(C_174))), inference(resolution, [status(thm)], [c_237, c_26])).
% 7.24/2.45  tff(c_1007, plain, (![B_173, A_172, C_174]: (k1_partfun1(k1_relat_1('#skF_3'), '#skF_3', B_173, A_172, '#skF_3', k2_funct_1(C_174))=k5_relat_1('#skF_3', k2_funct_1(C_174)) | ~v1_funct_1(k2_funct_1(C_174)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_172, B_173, C_174)!=B_173 | ~v2_funct_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_2(C_174, A_172, B_173) | ~v1_funct_1(C_174))), inference(resolution, [status(thm)], [c_708, c_1005])).
% 7.24/2.45  tff(c_1014, plain, (![B_175, A_176, C_177]: (k1_partfun1(k1_relat_1('#skF_3'), '#skF_3', B_175, A_176, '#skF_3', k2_funct_1(C_177))=k5_relat_1('#skF_3', k2_funct_1(C_177)) | ~v1_funct_1(k2_funct_1(C_177)) | k2_relset_1(A_176, B_175, C_177)!=B_175 | ~v2_funct_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_176, B_175))) | ~v1_funct_2(C_177, A_176, B_175) | ~v1_funct_1(C_177))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1007])).
% 7.24/2.45  tff(c_1017, plain, (k1_partfun1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3', k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_708, c_1014])).
% 7.24/2.45  tff(c_1023, plain, (k1_partfun1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3', k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_712, c_46, c_709, c_208, c_1017])).
% 7.24/2.45  tff(c_822, plain, (k1_partfun1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3', k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_704, c_704, c_322])).
% 7.24/2.45  tff(c_1025, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_822])).
% 7.24/2.45  tff(c_1032, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_60, c_1025])).
% 7.24/2.45  tff(c_1036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_1032])).
% 7.24/2.45  tff(c_1038, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_318])).
% 7.24/2.45  tff(c_212, plain, (![C_61, B_62, A_63]: (v1_funct_2(k2_funct_1(C_61), B_62, A_63) | k2_relset_1(A_63, B_62, C_61)!=B_62 | ~v2_funct_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))) | ~v1_funct_2(C_61, A_63, B_62) | ~v1_funct_1(C_61))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.24/2.45  tff(c_215, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_161, c_212])).
% 7.24/2.45  tff(c_218, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_162, c_46, c_163, c_215])).
% 7.24/2.45  tff(c_1085, plain, (![B_181, A_182, C_183]: (k1_relset_1(B_181, A_182, k2_funct_1(C_183))=k1_relat_1(k2_funct_1(C_183)) | k2_relset_1(A_182, B_181, C_183)!=B_181 | ~v2_funct_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_182, B_181))) | ~v1_funct_2(C_183, A_182, B_181) | ~v1_funct_1(C_183))), inference(resolution, [status(thm)], [c_237, c_12])).
% 7.24/2.45  tff(c_1091, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_161, c_1085])).
% 7.24/2.45  tff(c_1095, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_162, c_46, c_163, c_1091])).
% 7.24/2.45  tff(c_1137, plain, (![A_191, B_192, C_193]: (k1_xboole_0=A_191 | k1_relset_1(B_192, A_191, k2_funct_1(C_193))=B_192 | ~v1_funct_2(k2_funct_1(C_193), B_192, A_191) | k2_relset_1(A_191, B_192, C_193)!=B_192 | ~v2_funct_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))) | ~v1_funct_2(C_193, A_191, B_192) | ~v1_funct_1(C_193))), inference(resolution, [status(thm)], [c_237, c_24])).
% 7.24/2.45  tff(c_1143, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_161, c_1137])).
% 7.24/2.45  tff(c_1147, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1(k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_162, c_46, c_163, c_218, c_1095, c_1143])).
% 7.24/2.45  tff(c_1148, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1147])).
% 7.24/2.45  tff(c_1153, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1148, c_4])).
% 7.24/2.45  tff(c_1160, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_1153])).
% 7.24/2.45  tff(c_1175, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1160, c_162])).
% 7.24/2.45  tff(c_1176, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1160, c_161])).
% 7.24/2.45  tff(c_1174, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1160, c_1160, c_163])).
% 7.24/2.45  tff(c_1075, plain, (![A_178, C_179, B_180]: (k6_partfun1(A_178)=k5_relat_1(C_179, k2_funct_1(C_179)) | k1_xboole_0=B_180 | ~v2_funct_1(C_179) | k2_relset_1(A_178, B_180, C_179)!=B_180 | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_180))) | ~v1_funct_2(C_179, A_178, B_180) | ~v1_funct_1(C_179))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.24/2.45  tff(c_1079, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k2_struct_0('#skF_2')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_161, c_1075])).
% 7.24/2.45  tff(c_1083, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_162, c_163, c_46, c_1079])).
% 7.24/2.45  tff(c_1084, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1038, c_1083])).
% 7.24/2.45  tff(c_1327, plain, (![E_205, A_206, B_203, A_204, B_207, C_208]: (k1_partfun1(A_204, B_203, B_207, A_206, E_205, k2_funct_1(C_208))=k5_relat_1(E_205, k2_funct_1(C_208)) | ~v1_funct_1(k2_funct_1(C_208)) | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_1(E_205) | k2_relset_1(A_206, B_207, C_208)!=B_207 | ~v2_funct_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_2(C_208, A_206, B_207) | ~v1_funct_1(C_208))), inference(resolution, [status(thm)], [c_237, c_26])).
% 7.24/2.45  tff(c_1329, plain, (![B_207, A_206, C_208]: (k1_partfun1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), B_207, A_206, '#skF_3', k2_funct_1(C_208))=k5_relat_1('#skF_3', k2_funct_1(C_208)) | ~v1_funct_1(k2_funct_1(C_208)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_206, B_207, C_208)!=B_207 | ~v2_funct_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_2(C_208, A_206, B_207) | ~v1_funct_1(C_208))), inference(resolution, [status(thm)], [c_1176, c_1327])).
% 7.24/2.45  tff(c_1345, plain, (![B_212, A_213, C_214]: (k1_partfun1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), B_212, A_213, '#skF_3', k2_funct_1(C_214))=k5_relat_1('#skF_3', k2_funct_1(C_214)) | ~v1_funct_1(k2_funct_1(C_214)) | k2_relset_1(A_213, B_212, C_214)!=B_212 | ~v2_funct_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_213, B_212))) | ~v1_funct_2(C_214, A_213, B_212) | ~v1_funct_1(C_214))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1329])).
% 7.24/2.45  tff(c_1170, plain, (k1_partfun1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1160, c_1160, c_226])).
% 7.24/2.45  tff(c_1351, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1345, c_1170])).
% 7.24/2.45  tff(c_1358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1175, c_1176, c_46, c_1174, c_208, c_1084, c_1351])).
% 7.24/2.45  tff(c_1359, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1147])).
% 7.24/2.45  tff(c_1371, plain, (v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_162])).
% 7.24/2.45  tff(c_1370, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_163])).
% 7.24/2.45  tff(c_1368, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_218])).
% 7.24/2.45  tff(c_1372, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_161])).
% 7.24/2.45  tff(c_281, plain, (![C_73, B_74]: (k2_funct_1(C_73)=k1_xboole_0 | ~v1_funct_2(k2_funct_1(C_73), B_74, k1_xboole_0) | k1_xboole_0=B_74 | k2_relset_1(k1_xboole_0, B_74, C_73)!=B_74 | ~v2_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_74))) | ~v1_funct_2(C_73, k1_xboole_0, B_74) | ~v1_funct_1(C_73))), inference(resolution, [status(thm)], [c_237, c_16])).
% 7.24/2.45  tff(c_1427, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_xboole_0) | k2_struct_0('#skF_2')=k1_xboole_0 | k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1372, c_281])).
% 7.24/2.45  tff(c_1476, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1371, c_46, c_1370, c_1368, c_1427])).
% 7.24/2.45  tff(c_1477, plain, (k2_funct_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1038, c_1476])).
% 7.24/2.45  tff(c_1366, plain, (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_1359, c_1359, c_226])).
% 7.24/2.45  tff(c_1610, plain, (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3', k1_xboole_0)!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1477, c_1366])).
% 7.24/2.45  tff(c_1527, plain, (v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1477, c_208])).
% 7.24/2.45  tff(c_1363, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_1084])).
% 7.24/2.45  tff(c_1522, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1477, c_1363])).
% 7.24/2.45  tff(c_1557, plain, (![B_222, A_221, C_223, B_218, A_219, E_220]: (k1_partfun1(A_219, B_218, B_222, A_221, E_220, k2_funct_1(C_223))=k5_relat_1(E_220, k2_funct_1(C_223)) | ~v1_funct_1(k2_funct_1(C_223)) | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1(A_219, B_218))) | ~v1_funct_1(E_220) | k2_relset_1(A_221, B_222, C_223)!=B_222 | ~v2_funct_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~v1_funct_2(C_223, A_221, B_222) | ~v1_funct_1(C_223))), inference(resolution, [status(thm)], [c_237, c_26])).
% 7.24/2.45  tff(c_1559, plain, (![B_222, A_221, C_223]: (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), B_222, A_221, '#skF_3', k2_funct_1(C_223))=k5_relat_1('#skF_3', k2_funct_1(C_223)) | ~v1_funct_1(k2_funct_1(C_223)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_221, B_222, C_223)!=B_222 | ~v2_funct_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~v1_funct_2(C_223, A_221, B_222) | ~v1_funct_1(C_223))), inference(resolution, [status(thm)], [c_1372, c_1557])).
% 7.24/2.45  tff(c_1774, plain, (![B_236, A_237, C_238]: (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), B_236, A_237, '#skF_3', k2_funct_1(C_238))=k5_relat_1('#skF_3', k2_funct_1(C_238)) | ~v1_funct_1(k2_funct_1(C_238)) | k2_relset_1(A_237, B_236, C_238)!=B_236 | ~v2_funct_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_237, B_236))) | ~v1_funct_2(C_238, A_237, B_236) | ~v1_funct_1(C_238))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1559])).
% 7.24/2.45  tff(c_1780, plain, (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1372, c_1774])).
% 7.24/2.45  tff(c_1789, plain, (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3', k1_xboole_0)=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1371, c_46, c_1370, c_1527, c_1477, c_1522, c_1477, c_1477, c_1780])).
% 7.24/2.45  tff(c_1791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1610, c_1789])).
% 7.24/2.45  tff(c_1792, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_158])).
% 7.24/2.45  tff(c_1796, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1792, c_94])).
% 7.24/2.45  tff(c_1795, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1792, c_95])).
% 7.24/2.45  tff(c_1824, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_1795, c_16])).
% 7.24/2.45  tff(c_1840, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1796, c_1824])).
% 7.24/2.45  tff(c_1845, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1840])).
% 7.24/2.45  tff(c_1793, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_158])).
% 7.24/2.45  tff(c_1852, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_1793])).
% 7.24/2.45  tff(c_1851, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_1796])).
% 7.24/2.45  tff(c_1848, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_1795])).
% 7.24/2.45  tff(c_1878, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_1848, c_22])).
% 7.24/2.45  tff(c_1903, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1851, c_1878])).
% 7.24/2.45  tff(c_1794, plain, (k1_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1792, c_123])).
% 7.24/2.45  tff(c_1849, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_1794])).
% 7.24/2.45  tff(c_1917, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1903, c_1849])).
% 7.24/2.45  tff(c_1918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1852, c_1917])).
% 7.24/2.45  tff(c_1919, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1840])).
% 7.24/2.45  tff(c_1925, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1919, c_1796])).
% 7.24/2.45  tff(c_1797, plain, (k2_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1792, c_1792, c_89])).
% 7.24/2.45  tff(c_1924, plain, (k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1919, c_1919, c_1797])).
% 7.24/2.45  tff(c_1921, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1919, c_1795])).
% 7.24/2.45  tff(c_34, plain, (![C_21, A_19, B_20]: (v1_funct_1(k2_funct_1(C_21)) | k2_relset_1(A_19, B_20, C_21)!=B_20 | ~v2_funct_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.24/2.45  tff(c_1953, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1921, c_34])).
% 7.24/2.45  tff(c_1962, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1925, c_46, c_1924, c_1953])).
% 7.24/2.45  tff(c_2037, plain, (![C_276, B_277, A_278]: (m1_subset_1(k2_funct_1(C_276), k1_zfmisc_1(k2_zfmisc_1(B_277, A_278))) | k2_relset_1(A_278, B_277, C_276)!=B_277 | ~v2_funct_1(C_276) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_278, B_277))) | ~v1_funct_2(C_276, A_278, B_277) | ~v1_funct_1(C_276))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.24/2.45  tff(c_2242, plain, (![A_315, A_318, B_317, C_314, E_316, B_313]: (k1_partfun1(A_315, B_313, B_317, A_318, E_316, k2_funct_1(C_314))=k5_relat_1(E_316, k2_funct_1(C_314)) | ~v1_funct_1(k2_funct_1(C_314)) | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(A_315, B_313))) | ~v1_funct_1(E_316) | k2_relset_1(A_318, B_317, C_314)!=B_317 | ~v2_funct_1(C_314) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_318, B_317))) | ~v1_funct_2(C_314, A_318, B_317) | ~v1_funct_1(C_314))), inference(resolution, [status(thm)], [c_2037, c_26])).
% 7.24/2.45  tff(c_2246, plain, (![B_317, A_318, C_314]: (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', B_317, A_318, '#skF_3', k2_funct_1(C_314))=k5_relat_1('#skF_3', k2_funct_1(C_314)) | ~v1_funct_1(k2_funct_1(C_314)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_318, B_317, C_314)!=B_317 | ~v2_funct_1(C_314) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_318, B_317))) | ~v1_funct_2(C_314, A_318, B_317) | ~v1_funct_1(C_314))), inference(resolution, [status(thm)], [c_1921, c_2242])).
% 7.24/2.45  tff(c_2251, plain, (![B_319, A_320, C_321]: (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', B_319, A_320, '#skF_3', k2_funct_1(C_321))=k5_relat_1('#skF_3', k2_funct_1(C_321)) | ~v1_funct_1(k2_funct_1(C_321)) | k2_relset_1(A_320, B_319, C_321)!=B_319 | ~v2_funct_1(C_321) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_320, B_319))) | ~v1_funct_2(C_321, A_320, B_319) | ~v1_funct_1(C_321))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2246])).
% 7.24/2.45  tff(c_2257, plain, (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1921, c_2251])).
% 7.24/2.45  tff(c_2261, plain, (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1925, c_46, c_1924, c_1962, c_2257])).
% 7.24/2.45  tff(c_2003, plain, (![A_261, B_262, C_263]: (k2_tops_2(A_261, B_262, C_263)=k2_funct_1(C_263) | ~v2_funct_1(C_263) | k2_relset_1(A_261, B_262, C_263)!=B_262 | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_2(C_263, A_261, B_262) | ~v1_funct_1(C_263))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.24/2.45  tff(c_2006, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1921, c_2003])).
% 7.24/2.45  tff(c_2009, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1925, c_1924, c_46, c_2006])).
% 7.24/2.45  tff(c_1927, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1919, c_1792])).
% 7.24/2.45  tff(c_1966, plain, (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_1927, c_1927, c_130])).
% 7.24/2.45  tff(c_2010, plain, (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2009, c_1966])).
% 7.24/2.45  tff(c_2262, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2261, c_2010])).
% 7.24/2.45  tff(c_2269, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_60, c_2262])).
% 7.24/2.45  tff(c_2273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_2269])).
% 7.24/2.45  tff(c_2274, plain, (k1_partfun1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_129])).
% 7.24/2.45  tff(c_2305, plain, (k1_partfun1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2304, c_2304, c_2304, c_2274])).
% 7.24/2.45  tff(c_2376, plain, (k1_partfun1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2375, c_2305])).
% 7.24/2.45  tff(c_2478, plain, (k1_partfun1(k1_xboole_0, k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), k1_xboole_0, k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2474, c_2474, c_2474, c_2376])).
% 7.24/2.45  tff(c_2713, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2581, c_2581, c_2478])).
% 7.24/2.45  tff(c_2798, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2792, c_2713])).
% 7.24/2.45  tff(c_2805, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1(k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_61, c_2798])).
% 7.24/2.45  tff(c_2808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_2773, c_2805])).
% 7.24/2.45  tff(c_2809, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2566])).
% 7.24/2.45  tff(c_2816, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2484])).
% 7.24/2.45  tff(c_2817, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2809, c_2483])).
% 7.24/2.45  tff(c_2815, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2480])).
% 7.24/2.45  tff(c_2812, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2482])).
% 7.24/2.45  tff(c_2855, plain, (k1_relset_1('#skF_3', k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2812, c_2452])).
% 7.24/2.45  tff(c_2878, plain, (k1_relset_1('#skF_3', k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2816, c_46, c_2817, c_2855])).
% 7.24/2.45  tff(c_2449, plain, (![A_356, C_354]: (k1_relset_1(k1_xboole_0, A_356, k2_funct_1(C_354))=k1_xboole_0 | ~v1_funct_2(k2_funct_1(C_354), k1_xboole_0, A_356) | k2_relset_1(A_356, k1_xboole_0, C_354)!=k1_xboole_0 | ~v2_funct_1(C_354) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_356, k1_xboole_0))) | ~v1_funct_2(C_354, A_356, k1_xboole_0) | ~v1_funct_1(C_354))), inference(resolution, [status(thm)], [c_2403, c_22])).
% 7.24/2.45  tff(c_2971, plain, (![A_394, C_395]: (k1_relset_1('#skF_3', A_394, k2_funct_1(C_395))='#skF_3' | ~v1_funct_2(k2_funct_1(C_395), '#skF_3', A_394) | k2_relset_1(A_394, '#skF_3', C_395)!='#skF_3' | ~v2_funct_1(C_395) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(A_394, '#skF_3'))) | ~v1_funct_2(C_395, A_394, '#skF_3') | ~v1_funct_1(C_395))), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2809, c_2809, c_2809, c_2809, c_2809, c_2809, c_2449])).
% 7.24/2.45  tff(c_2974, plain, (k1_relset_1('#skF_3', k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2812, c_2971])).
% 7.24/2.45  tff(c_2981, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2816, c_46, c_2817, c_2815, c_2878, c_2974])).
% 7.24/2.45  tff(c_2987, plain, (k2_relat_1('#skF_3')='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2981, c_4])).
% 7.24/2.45  tff(c_2994, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_2987])).
% 7.24/2.45  tff(c_2819, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2474])).
% 7.24/2.45  tff(c_3066, plain, (![B_411, A_412, C_413]: (k1_partfun1(B_411, A_412, k1_relat_1('#skF_3'), '#skF_3', k2_funct_1(C_413), '#skF_3')=k5_relat_1(k2_funct_1(C_413), '#skF_3') | ~v1_funct_1(k2_funct_1(C_413)) | k2_relset_1(A_412, B_411, C_413)!=B_411 | ~v2_funct_1(C_413) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_412, B_411))) | ~v1_funct_2(C_413, A_412, B_411) | ~v1_funct_1(C_413))), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_2442])).
% 7.24/2.45  tff(c_3069, plain, (k1_partfun1('#skF_3', k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2812, c_3066])).
% 7.24/2.45  tff(c_3075, plain, (k1_partfun1('#skF_3', k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2816, c_46, c_2817, c_2361, c_3069])).
% 7.24/2.45  tff(c_2914, plain, (k1_partfun1('#skF_3', k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2809, c_2809, c_2478])).
% 7.24/2.45  tff(c_3077, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3075, c_2914])).
% 7.24/2.45  tff(c_3084, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_61, c_3077])).
% 7.24/2.45  tff(c_3087, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_2994, c_3084])).
% 7.24/2.45  tff(c_3089, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2473])).
% 7.24/2.45  tff(c_3106, plain, (![B_414, C_415, A_416]: (k6_partfun1(B_414)=k5_relat_1(k2_funct_1(C_415), C_415) | k1_xboole_0=B_414 | ~v2_funct_1(C_415) | k2_relset_1(A_416, B_414, C_415)!=B_414 | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_416, B_414))) | ~v1_funct_2(C_415, A_416, B_414) | ~v1_funct_1(C_415))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.24/2.45  tff(c_3110, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2307, c_3106])).
% 7.24/2.45  tff(c_3114, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2308, c_2309, c_46, c_3110])).
% 7.24/2.45  tff(c_3115, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_3089, c_3114])).
% 7.24/2.45  tff(c_3130, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k6_partfun1(k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3115, c_61])).
% 7.24/2.45  tff(c_3137, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_3130])).
% 7.24/2.45  tff(c_3141, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3137, c_3115])).
% 7.24/2.45  tff(c_3395, plain, (![B_442, A_443, C_444]: (k1_partfun1(B_442, A_443, k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(C_444), '#skF_3')=k5_relat_1(k2_funct_1(C_444), '#skF_3') | ~v1_funct_1(k2_funct_1(C_444)) | k2_relset_1(A_443, B_442, C_444)!=B_442 | ~v2_funct_1(C_444) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_443, B_442))) | ~v1_funct_2(C_444, A_443, B_442) | ~v1_funct_1(C_444))), inference(demodulation, [status(thm), theory('equality')], [c_3214, c_2442])).
% 7.24/2.45  tff(c_3142, plain, (k1_partfun1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3137, c_2376])).
% 7.24/2.45  tff(c_3219, plain, (k1_partfun1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3214, c_3214, c_3142])).
% 7.24/2.45  tff(c_3401, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3395, c_3219])).
% 7.24/2.45  tff(c_3408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_3230, c_3228, c_46, c_3229, c_2361, c_3141, c_3401])).
% 7.24/2.45  tff(c_3409, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3190])).
% 7.24/2.45  tff(c_3422, plain, (v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3409, c_2308])).
% 7.24/2.45  tff(c_3421, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3409, c_2309])).
% 7.24/2.45  tff(c_3418, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3409, c_2368])).
% 7.24/2.45  tff(c_3420, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_3409, c_2307])).
% 7.24/2.45  tff(c_2451, plain, (![C_354, B_355]: (k2_funct_1(C_354)=k1_xboole_0 | ~v1_funct_2(k2_funct_1(C_354), B_355, k1_xboole_0) | k1_xboole_0=B_355 | k2_relset_1(k1_xboole_0, B_355, C_354)!=B_355 | ~v2_funct_1(C_354) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_355))) | ~v1_funct_2(C_354, k1_xboole_0, B_355) | ~v1_funct_1(C_354))), inference(resolution, [status(thm)], [c_2403, c_16])).
% 7.24/2.45  tff(c_3451, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_xboole_0) | k2_struct_0('#skF_2')=k1_xboole_0 | k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3420, c_2451])).
% 7.24/2.45  tff(c_3500, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_xboole_0) | k2_struct_0('#skF_2')=k1_xboole_0 | k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_3451])).
% 7.24/2.45  tff(c_3501, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_xboole_0) | k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_3089, c_3500])).
% 7.24/2.45  tff(c_3638, plain, (k2_funct_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3422, c_3421, c_3418, c_3501])).
% 7.24/2.45  tff(c_3665, plain, (k2_relat_1('#skF_3')=k1_relat_1(k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3638, c_4])).
% 7.24/2.45  tff(c_3680, plain, (k2_relat_1('#skF_3')=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_3665])).
% 7.24/2.45  tff(c_3647, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k5_relat_1(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3638, c_3141])).
% 7.24/2.45  tff(c_3714, plain, (k6_partfun1(k1_relat_1(k1_xboole_0))=k5_relat_1(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3680, c_3647])).
% 7.24/2.45  tff(c_3411, plain, (k1_partfun1(k2_struct_0('#skF_2'), k1_xboole_0, k1_xboole_0, k2_struct_0('#skF_2'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3409, c_3409, c_3142])).
% 7.24/2.45  tff(c_3640, plain, (k1_partfun1(k2_struct_0('#skF_2'), k1_xboole_0, k1_xboole_0, k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3638, c_3411])).
% 7.24/2.45  tff(c_3744, plain, (k1_partfun1(k2_struct_0('#skF_2'), k1_xboole_0, k1_xboole_0, k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3')!=k5_relat_1(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3714, c_3680, c_3640])).
% 7.24/2.45  tff(c_3649, plain, (v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3638, c_2361])).
% 7.24/2.45  tff(c_30, plain, (![C_21, B_20, A_19]: (m1_subset_1(k2_funct_1(C_21), k1_zfmisc_1(k2_zfmisc_1(B_20, A_19))) | k2_relset_1(A_19, B_20, C_21)!=B_20 | ~v2_funct_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.24/2.45  tff(c_3656, plain, (![B_20, A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(B_20, A_19))) | k2_relset_1(A_19, B_20, '#skF_3')!=B_20 | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2('#skF_3', A_19, B_20) | ~v1_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3638, c_30])).
% 7.24/2.45  tff(c_3745, plain, (![B_469, A_470]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(B_469, A_470))) | k2_relset_1(A_470, B_469, '#skF_3')!=B_469 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_470, B_469))) | ~v1_funct_2('#skF_3', A_470, B_469))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_3656])).
% 7.24/2.45  tff(c_3415, plain, (![A_346, B_345, E_347]: (k1_partfun1(A_346, B_345, k1_xboole_0, k2_struct_0('#skF_2'), E_347, '#skF_3')=k5_relat_1(E_347, '#skF_3') | ~m1_subset_1(E_347, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))) | ~v1_funct_1(E_347))), inference(demodulation, [status(thm), theory('equality')], [c_3409, c_2391])).
% 7.24/2.45  tff(c_3755, plain, (![B_469, A_470]: (k1_partfun1(B_469, A_470, k1_xboole_0, k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3')=k5_relat_1(k1_xboole_0, '#skF_3') | ~v1_funct_1(k1_xboole_0) | k2_relset_1(A_470, B_469, '#skF_3')!=B_469 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_470, B_469))) | ~v1_funct_2('#skF_3', A_470, B_469))), inference(resolution, [status(thm)], [c_3745, c_3415])).
% 7.24/2.45  tff(c_3955, plain, (![B_486, A_487]: (k1_partfun1(B_486, A_487, k1_xboole_0, k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3')=k5_relat_1(k1_xboole_0, '#skF_3') | k2_relset_1(A_487, B_486, '#skF_3')!=B_486 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_487, B_486))) | ~v1_funct_2('#skF_3', A_487, B_486))), inference(demodulation, [status(thm), theory('equality')], [c_3649, c_3755])).
% 7.24/2.45  tff(c_3958, plain, (k1_partfun1(k2_struct_0('#skF_2'), k1_xboole_0, k1_xboole_0, k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3')=k5_relat_1(k1_xboole_0, '#skF_3') | k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3420, c_3955])).
% 7.24/2.45  tff(c_3961, plain, (k1_partfun1(k2_struct_0('#skF_2'), k1_xboole_0, k1_xboole_0, k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3')=k5_relat_1(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3422, c_3421, c_3958])).
% 7.24/2.45  tff(c_3963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3744, c_3961])).
% 7.24/2.45  tff(c_3964, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2303])).
% 7.24/2.45  tff(c_3968, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3964, c_94])).
% 7.24/2.45  tff(c_3967, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_3964, c_95])).
% 7.24/2.45  tff(c_3988, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_3967, c_16])).
% 7.24/2.45  tff(c_4001, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3968, c_3988])).
% 7.24/2.45  tff(c_4005, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4001])).
% 7.24/2.45  tff(c_3965, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2303])).
% 7.24/2.45  tff(c_4008, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4005, c_3965])).
% 7.24/2.45  tff(c_4007, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4005, c_3968])).
% 7.24/2.45  tff(c_4006, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_4005, c_3967])).
% 7.24/2.45  tff(c_4032, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_4006, c_22])).
% 7.24/2.45  tff(c_4054, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4007, c_4032])).
% 7.24/2.45  tff(c_4061, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4006, c_12])).
% 7.24/2.45  tff(c_4068, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_4061])).
% 7.24/2.45  tff(c_4069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4008, c_4068])).
% 7.24/2.45  tff(c_4070, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4001])).
% 7.24/2.45  tff(c_4073, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4070, c_3968])).
% 7.24/2.45  tff(c_3969, plain, (k2_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3964, c_3964, c_89])).
% 7.24/2.45  tff(c_4074, plain, (k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4070, c_4070, c_3969])).
% 7.24/2.45  tff(c_4072, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4070, c_3967])).
% 7.24/2.45  tff(c_4162, plain, (![C_507, B_508, A_509]: (v1_funct_2(k2_funct_1(C_507), B_508, A_509) | k2_relset_1(A_509, B_508, C_507)!=B_508 | ~v2_funct_1(C_507) | ~m1_subset_1(C_507, k1_zfmisc_1(k2_zfmisc_1(A_509, B_508))) | ~v1_funct_2(C_507, A_509, B_508) | ~v1_funct_1(C_507))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.24/2.45  tff(c_4165, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4072, c_4162])).
% 7.24/2.45  tff(c_4168, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4073, c_46, c_4074, c_4165])).
% 7.24/2.45  tff(c_4176, plain, (![C_513, B_514, A_515]: (m1_subset_1(k2_funct_1(C_513), k1_zfmisc_1(k2_zfmisc_1(B_514, A_515))) | k2_relset_1(A_515, B_514, C_513)!=B_514 | ~v2_funct_1(C_513) | ~m1_subset_1(C_513, k1_zfmisc_1(k2_zfmisc_1(A_515, B_514))) | ~v1_funct_2(C_513, A_515, B_514) | ~v1_funct_1(C_513))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.24/2.45  tff(c_4287, plain, (![B_534, A_535, C_536]: (k1_relset_1(B_534, A_535, k2_funct_1(C_536))=k1_relat_1(k2_funct_1(C_536)) | k2_relset_1(A_535, B_534, C_536)!=B_534 | ~v2_funct_1(C_536) | ~m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(A_535, B_534))) | ~v1_funct_2(C_536, A_535, B_534) | ~v1_funct_1(C_536))), inference(resolution, [status(thm)], [c_4176, c_12])).
% 7.24/2.45  tff(c_4293, plain, (k1_relset_1('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4072, c_4287])).
% 7.24/2.45  tff(c_4297, plain, (k1_relset_1('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4073, c_46, c_4074, c_4293])).
% 7.24/2.45  tff(c_4078, plain, (![B_10, C_11]: (k1_relset_1('#skF_3', B_10, C_11)='#skF_3' | ~v1_funct_2(C_11, '#skF_3', B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_10))))), inference(demodulation, [status(thm), theory('equality')], [c_4070, c_4070, c_4070, c_4070, c_22])).
% 7.24/2.45  tff(c_4329, plain, (![A_542, C_543]: (k1_relset_1('#skF_3', A_542, k2_funct_1(C_543))='#skF_3' | ~v1_funct_2(k2_funct_1(C_543), '#skF_3', A_542) | k2_relset_1(A_542, '#skF_3', C_543)!='#skF_3' | ~v2_funct_1(C_543) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_542, '#skF_3'))) | ~v1_funct_2(C_543, A_542, '#skF_3') | ~v1_funct_1(C_543))), inference(resolution, [status(thm)], [c_4176, c_4078])).
% 7.24/2.45  tff(c_4336, plain, (k1_relset_1('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4072, c_4329])).
% 7.24/2.45  tff(c_4340, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4073, c_46, c_4074, c_4168, c_4297, c_4336])).
% 7.24/2.45  tff(c_4345, plain, (k2_relat_1('#skF_3')='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4340, c_4])).
% 7.24/2.45  tff(c_4352, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_4345])).
% 7.24/2.45  tff(c_4138, plain, (![C_497, A_498, B_499]: (v1_funct_1(k2_funct_1(C_497)) | k2_relset_1(A_498, B_499, C_497)!=B_499 | ~v2_funct_1(C_497) | ~m1_subset_1(C_497, k1_zfmisc_1(k2_zfmisc_1(A_498, B_499))) | ~v1_funct_2(C_497, A_498, B_499) | ~v1_funct_1(C_497))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.24/2.45  tff(c_4141, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4072, c_4138])).
% 7.24/2.45  tff(c_4144, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4073, c_46, c_4074, c_4141])).
% 7.24/2.45  tff(c_4230, plain, (![A_517, F_520, B_516, C_521, D_519, E_518]: (k1_partfun1(A_517, B_516, C_521, D_519, E_518, F_520)=k5_relat_1(E_518, F_520) | ~m1_subset_1(F_520, k1_zfmisc_1(k2_zfmisc_1(C_521, D_519))) | ~v1_funct_1(F_520) | ~m1_subset_1(E_518, k1_zfmisc_1(k2_zfmisc_1(A_517, B_516))) | ~v1_funct_1(E_518))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.24/2.45  tff(c_4234, plain, (![A_517, B_516, E_518]: (k1_partfun1(A_517, B_516, k2_struct_0('#skF_1'), '#skF_3', E_518, '#skF_3')=k5_relat_1(E_518, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_518, k1_zfmisc_1(k2_zfmisc_1(A_517, B_516))) | ~v1_funct_1(E_518))), inference(resolution, [status(thm)], [c_4072, c_4230])).
% 7.24/2.45  tff(c_4239, plain, (![A_522, B_523, E_524]: (k1_partfun1(A_522, B_523, k2_struct_0('#skF_1'), '#skF_3', E_524, '#skF_3')=k5_relat_1(E_524, '#skF_3') | ~m1_subset_1(E_524, k1_zfmisc_1(k2_zfmisc_1(A_522, B_523))) | ~v1_funct_1(E_524))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4234])).
% 7.24/2.45  tff(c_4308, plain, (![B_539, A_540, C_541]: (k1_partfun1(B_539, A_540, k2_struct_0('#skF_1'), '#skF_3', k2_funct_1(C_541), '#skF_3')=k5_relat_1(k2_funct_1(C_541), '#skF_3') | ~v1_funct_1(k2_funct_1(C_541)) | k2_relset_1(A_540, B_539, C_541)!=B_539 | ~v2_funct_1(C_541) | ~m1_subset_1(C_541, k1_zfmisc_1(k2_zfmisc_1(A_540, B_539))) | ~v1_funct_2(C_541, A_540, B_539) | ~v1_funct_1(C_541))), inference(resolution, [status(thm)], [c_30, c_4239])).
% 7.24/2.45  tff(c_4314, plain, (k1_partfun1('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4072, c_4308])).
% 7.24/2.45  tff(c_4318, plain, (k1_partfun1('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4073, c_46, c_4074, c_4144, c_4314])).
% 7.24/2.45  tff(c_4169, plain, (![A_510, B_511, C_512]: (k2_tops_2(A_510, B_511, C_512)=k2_funct_1(C_512) | ~v2_funct_1(C_512) | k2_relset_1(A_510, B_511, C_512)!=B_511 | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(A_510, B_511))) | ~v1_funct_2(C_512, A_510, B_511) | ~v1_funct_1(C_512))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.24/2.45  tff(c_4172, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4072, c_4169])).
% 7.24/2.45  tff(c_4175, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4073, c_4074, c_46, c_4172])).
% 7.24/2.45  tff(c_4076, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4070, c_3964])).
% 7.24/2.45  tff(c_4161, plain, (k1_partfun1('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3'), '#skF_3')!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4076, c_4076, c_4076, c_4076, c_2274])).
% 7.24/2.45  tff(c_4220, plain, (k1_partfun1('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4175, c_4161])).
% 7.24/2.45  tff(c_4319, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4318, c_4220])).
% 7.24/2.45  tff(c_4326, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_61, c_4319])).
% 7.24/2.45  tff(c_4328, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_46, c_4326])).
% 7.24/2.45  tff(c_4369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4352, c_4328])).
% 7.24/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/2.45  
% 7.24/2.45  Inference rules
% 7.24/2.45  ----------------------
% 7.24/2.45  #Ref     : 0
% 7.24/2.45  #Sup     : 938
% 7.24/2.45  #Fact    : 0
% 7.24/2.45  #Define  : 0
% 7.24/2.45  #Split   : 18
% 7.24/2.45  #Chain   : 0
% 7.24/2.45  #Close   : 0
% 7.24/2.45  
% 7.24/2.45  Ordering : KBO
% 7.24/2.45  
% 7.24/2.45  Simplification rules
% 7.24/2.45  ----------------------
% 7.24/2.45  #Subsume      : 80
% 7.24/2.45  #Demod        : 1657
% 7.24/2.45  #Tautology    : 604
% 7.24/2.45  #SimpNegUnit  : 41
% 7.24/2.45  #BackRed      : 222
% 7.24/2.45  
% 7.24/2.45  #Partial instantiations: 0
% 7.24/2.45  #Strategies tried      : 1
% 7.24/2.45  
% 7.24/2.45  Timing (in seconds)
% 7.24/2.45  ----------------------
% 7.24/2.46  Preprocessing        : 0.36
% 7.24/2.46  Parsing              : 0.19
% 7.24/2.46  CNF conversion       : 0.03
% 7.24/2.46  Main loop            : 1.18
% 7.24/2.46  Inferencing          : 0.42
% 7.24/2.46  Reduction            : 0.40
% 7.24/2.46  Demodulation         : 0.29
% 7.24/2.46  BG Simplification    : 0.05
% 7.24/2.46  Subsumption          : 0.22
% 7.24/2.46  Abstraction          : 0.07
% 7.24/2.46  MUC search           : 0.00
% 7.24/2.46  Cooper               : 0.00
% 7.24/2.46  Total                : 1.66
% 7.24/2.46  Index Insertion      : 0.00
% 7.24/2.46  Index Deletion       : 0.00
% 7.24/2.46  Index Matching       : 0.00
% 7.24/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
