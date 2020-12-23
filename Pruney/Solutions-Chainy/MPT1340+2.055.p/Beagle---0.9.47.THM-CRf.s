%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:38 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :  151 (5041 expanded)
%              Number of leaves         :   50 (1794 expanded)
%              Depth                    :   19
%              Number of atoms          :  340 (14645 expanded)
%              Number of equality atoms :   76 (3354 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_208,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_166,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_174,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_146,axiom,(
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

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_116,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_162,axiom,(
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

tff(f_64,axiom,(
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

tff(f_186,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_91,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_99,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_91])).

tff(c_72,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_98,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_91])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_131,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_98,c_66])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_134,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_131,c_4])).

tff(c_137,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_134])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_207,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_211,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_207])).

tff(c_64,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_124,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_98,c_64])).

tff(c_212,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_124])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_112,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(u1_struct_0(A_53))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_118,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_112])).

tff(c_122,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_118])).

tff(c_123,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_122])).

tff(c_221,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_123])).

tff(c_68,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_100,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_68])).

tff(c_109,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_100])).

tff(c_222,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_109])).

tff(c_220,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_131])).

tff(c_264,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_partfun1(C_71,A_72)
      | ~ v1_funct_2(C_71,A_72,B_73)
      | ~ v1_funct_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | v1_xboole_0(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_267,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_220,c_264])).

tff(c_270,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_222,c_267])).

tff(c_271,plain,(
    v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_270])).

tff(c_143,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_147,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_131,c_143])).

tff(c_200,plain,(
    ! [B_66,A_67] :
      ( k1_relat_1(B_66) = A_67
      | ~ v1_partfun1(B_66,A_67)
      | ~ v4_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_203,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_147,c_200])).

tff(c_206,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_203])).

tff(c_263,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_263])).

tff(c_274,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_278,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_222])).

tff(c_276,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_220])).

tff(c_691,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( r2_funct_2(A_116,B_117,C_118,C_118)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_2(D_119,A_116,B_117)
      | ~ v1_funct_1(D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_2(C_118,A_116,B_117)
      | ~ v1_funct_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_695,plain,(
    ! [C_118] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_118,C_118)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_118,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_276,c_691])).

tff(c_700,plain,(
    ! [C_120] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_120,C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_120,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_278,c_695])).

tff(c_705,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_276,c_700])).

tff(c_709,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_278,c_705])).

tff(c_24,plain,(
    ! [A_12] :
      ( k2_funct_1(k2_funct_1(A_12)) = A_12
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_217,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_211])).

tff(c_277,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_217])).

tff(c_356,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_funct_1(k2_funct_1(C_82))
      | k2_relset_1(A_83,B_84,C_82) != B_84
      | ~ v2_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_82,A_83,B_84)
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_359,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_276,c_356])).

tff(c_362,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_278,c_62,c_277,c_359])).

tff(c_363,plain,(
    ! [C_85,B_86,A_87] :
      ( v1_funct_2(k2_funct_1(C_85),B_86,A_87)
      | k2_relset_1(A_87,B_86,C_85) != B_86
      | ~ v2_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86)))
      | ~ v1_funct_2(C_85,A_87,B_86)
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_366,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_276,c_363])).

tff(c_369,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_278,c_62,c_277,c_366])).

tff(c_20,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_389,plain,(
    ! [C_92,B_93,A_94] :
      ( m1_subset_1(k2_funct_1(C_92),k1_zfmisc_1(k2_zfmisc_1(B_93,A_94)))
      | k2_relset_1(A_94,B_93,C_92) != B_93
      | ~ v2_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93)))
      | ~ v1_funct_2(C_92,A_94,B_93)
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_413,plain,(
    ! [C_92,B_93,A_94] :
      ( v1_relat_1(k2_funct_1(C_92))
      | ~ v1_relat_1(k2_zfmisc_1(B_93,A_94))
      | k2_relset_1(A_94,B_93,C_92) != B_93
      | ~ v2_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93)))
      | ~ v1_funct_2(C_92,A_94,B_93)
      | ~ v1_funct_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_389,c_4])).

tff(c_427,plain,(
    ! [C_95,A_96,B_97] :
      ( v1_relat_1(k2_funct_1(C_95))
      | k2_relset_1(A_96,B_97,C_95) != B_97
      | ~ v2_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_95,A_96,B_97)
      | ~ v1_funct_1(C_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_413])).

tff(c_433,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_276,c_427])).

tff(c_437,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_278,c_62,c_277,c_433])).

tff(c_40,plain,(
    ! [A_25] : k6_relat_1(A_25) = k6_partfun1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_14,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_438,plain,(
    ! [B_98,C_99,A_100] :
      ( k6_partfun1(B_98) = k5_relat_1(k2_funct_1(C_99),C_99)
      | k1_xboole_0 = B_98
      | ~ v2_funct_1(C_99)
      | k2_relset_1(A_100,B_98,C_99) != B_98
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_98)))
      | ~ v1_funct_2(C_99,A_100,B_98)
      | ~ v1_funct_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_442,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_276,c_438])).

tff(c_446,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_278,c_277,c_62,c_442])).

tff(c_447,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_446])).

tff(c_456,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_221])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_456])).

tff(c_461,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_18,plain,(
    ! [B_10,A_8] :
      ( v2_funct_1(B_10)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(k5_relat_1(B_10,A_8))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_469,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1(k2_relat_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_18])).

tff(c_475,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_70,c_437,c_362,c_77,c_469])).

tff(c_477,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_480,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_477])).

tff(c_484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_70,c_62,c_480])).

tff(c_486,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_30,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_relset_1(A_16,B_17,C_18) = k2_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_676,plain,(
    ! [B_113,A_114,C_115] :
      ( k2_relset_1(B_113,A_114,k2_funct_1(C_115)) = k2_relat_1(k2_funct_1(C_115))
      | k2_relset_1(A_114,B_113,C_115) != B_113
      | ~ v2_funct_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113)))
      | ~ v1_funct_2(C_115,A_114,B_113)
      | ~ v1_funct_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_389,c_30])).

tff(c_682,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_276,c_676])).

tff(c_686,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_278,c_62,c_277,c_486,c_682])).

tff(c_485,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_58,plain,(
    ! [A_38,B_39,C_40] :
      ( k2_tops_2(A_38,B_39,C_40) = k2_funct_1(C_40)
      | ~ v2_funct_1(C_40)
      | k2_relset_1(A_38,B_39,C_40) != B_39
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_2(C_40,A_38,B_39)
      | ~ v1_funct_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1207,plain,(
    ! [B_149,A_150,C_151] :
      ( k2_tops_2(B_149,A_150,k2_funct_1(C_151)) = k2_funct_1(k2_funct_1(C_151))
      | ~ v2_funct_1(k2_funct_1(C_151))
      | k2_relset_1(B_149,A_150,k2_funct_1(C_151)) != A_150
      | ~ v1_funct_2(k2_funct_1(C_151),B_149,A_150)
      | ~ v1_funct_1(k2_funct_1(C_151))
      | k2_relset_1(A_150,B_149,C_151) != B_149
      | ~ v2_funct_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_150,B_149)))
      | ~ v1_funct_2(C_151,A_150,B_149)
      | ~ v1_funct_1(C_151) ) ),
    inference(resolution,[status(thm)],[c_389,c_58])).

tff(c_1213,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_276,c_1207])).

tff(c_1217,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_278,c_62,c_277,c_362,c_369,c_686,c_485,c_1213])).

tff(c_370,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_tops_2(A_88,B_89,C_90) = k2_funct_1(C_90)
      | ~ v2_funct_1(C_90)
      | k2_relset_1(A_88,B_89,C_90) != B_89
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_2(C_90,A_88,B_89)
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_373,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_276,c_370])).

tff(c_376,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_278,c_277,c_62,c_373])).

tff(c_60,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_148,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_99,c_98,c_98,c_98,c_60])).

tff(c_218,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_212,c_212,c_148])).

tff(c_343,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_274,c_274,c_218])).

tff(c_377,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_343])).

tff(c_1218,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1217,c_377])).

tff(c_1225,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1218])).

tff(c_1228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_70,c_62,c_709,c_1225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.88  
% 4.34/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.88  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.34/1.88  
% 4.34/1.88  %Foreground sorts:
% 4.34/1.88  
% 4.34/1.88  
% 4.34/1.88  %Background operators:
% 4.34/1.88  
% 4.34/1.88  
% 4.34/1.88  %Foreground operators:
% 4.34/1.88  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.34/1.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.34/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.34/1.88  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.34/1.88  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.34/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.34/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.34/1.88  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.34/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.34/1.88  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.34/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.34/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.34/1.88  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.34/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.34/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.34/1.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.34/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.34/1.88  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.34/1.88  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.34/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.34/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.34/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.34/1.88  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.34/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.34/1.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.34/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.34/1.88  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.34/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.34/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.34/1.88  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.34/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.34/1.88  
% 4.74/1.92  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.74/1.92  tff(f_208, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 4.74/1.92  tff(f_166, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.74/1.92  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.74/1.92  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.74/1.92  tff(f_174, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.74/1.92  tff(f_106, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.74/1.92  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.74/1.92  tff(f_114, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.74/1.92  tff(f_130, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 4.74/1.92  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 4.74/1.92  tff(f_146, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.74/1.92  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.74/1.92  tff(f_116, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.74/1.92  tff(f_47, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.74/1.92  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.74/1.92  tff(f_162, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 4.74/1.92  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 4.74/1.92  tff(f_186, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 4.74/1.92  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.74/1.92  tff(c_76, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.74/1.92  tff(c_91, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.74/1.92  tff(c_99, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_91])).
% 4.74/1.92  tff(c_72, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.74/1.92  tff(c_98, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_91])).
% 4.74/1.92  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.74/1.92  tff(c_131, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_98, c_66])).
% 4.74/1.92  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.74/1.92  tff(c_134, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_131, c_4])).
% 4.74/1.92  tff(c_137, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_134])).
% 4.74/1.92  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.74/1.92  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.74/1.92  tff(c_207, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.74/1.92  tff(c_211, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_131, c_207])).
% 4.74/1.92  tff(c_64, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.74/1.92  tff(c_124, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_98, c_64])).
% 4.74/1.92  tff(c_212, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_124])).
% 4.74/1.92  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.74/1.92  tff(c_112, plain, (![A_53]: (~v1_xboole_0(u1_struct_0(A_53)) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_174])).
% 4.74/1.92  tff(c_118, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_98, c_112])).
% 4.74/1.92  tff(c_122, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_118])).
% 4.74/1.92  tff(c_123, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_74, c_122])).
% 4.74/1.92  tff(c_221, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_123])).
% 4.74/1.92  tff(c_68, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.74/1.92  tff(c_100, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_68])).
% 4.74/1.92  tff(c_109, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_100])).
% 4.74/1.92  tff(c_222, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_109])).
% 4.74/1.92  tff(c_220, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_131])).
% 4.74/1.92  tff(c_264, plain, (![C_71, A_72, B_73]: (v1_partfun1(C_71, A_72) | ~v1_funct_2(C_71, A_72, B_73) | ~v1_funct_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | v1_xboole_0(B_73))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.74/1.92  tff(c_267, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_220, c_264])).
% 4.74/1.92  tff(c_270, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_222, c_267])).
% 4.74/1.92  tff(c_271, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_221, c_270])).
% 4.74/1.92  tff(c_143, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.74/1.92  tff(c_147, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_131, c_143])).
% 4.74/1.92  tff(c_200, plain, (![B_66, A_67]: (k1_relat_1(B_66)=A_67 | ~v1_partfun1(B_66, A_67) | ~v4_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.74/1.92  tff(c_203, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_147, c_200])).
% 4.74/1.92  tff(c_206, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_203])).
% 4.74/1.92  tff(c_263, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_206])).
% 4.74/1.92  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_271, c_263])).
% 4.74/1.92  tff(c_274, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_206])).
% 4.74/1.92  tff(c_278, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_222])).
% 4.74/1.92  tff(c_276, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_220])).
% 4.74/1.92  tff(c_691, plain, (![A_116, B_117, C_118, D_119]: (r2_funct_2(A_116, B_117, C_118, C_118) | ~m1_subset_1(D_119, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_2(D_119, A_116, B_117) | ~v1_funct_1(D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_2(C_118, A_116, B_117) | ~v1_funct_1(C_118))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.74/1.92  tff(c_695, plain, (![C_118]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_118, C_118) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_118, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_118))), inference(resolution, [status(thm)], [c_276, c_691])).
% 4.74/1.92  tff(c_700, plain, (![C_120]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_120, C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_120, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_120))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_278, c_695])).
% 4.74/1.92  tff(c_705, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_276, c_700])).
% 4.74/1.92  tff(c_709, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_278, c_705])).
% 4.74/1.92  tff(c_24, plain, (![A_12]: (k2_funct_1(k2_funct_1(A_12))=A_12 | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.74/1.92  tff(c_217, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_211])).
% 4.74/1.92  tff(c_277, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_217])).
% 4.74/1.92  tff(c_356, plain, (![C_82, A_83, B_84]: (v1_funct_1(k2_funct_1(C_82)) | k2_relset_1(A_83, B_84, C_82)!=B_84 | ~v2_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_82, A_83, B_84) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.92  tff(c_359, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_276, c_356])).
% 4.74/1.92  tff(c_362, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_278, c_62, c_277, c_359])).
% 4.74/1.92  tff(c_363, plain, (![C_85, B_86, A_87]: (v1_funct_2(k2_funct_1(C_85), B_86, A_87) | k2_relset_1(A_87, B_86, C_85)!=B_86 | ~v2_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))) | ~v1_funct_2(C_85, A_87, B_86) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.92  tff(c_366, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_276, c_363])).
% 4.74/1.92  tff(c_369, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_278, c_62, c_277, c_366])).
% 4.74/1.92  tff(c_20, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.74/1.92  tff(c_389, plain, (![C_92, B_93, A_94]: (m1_subset_1(k2_funct_1(C_92), k1_zfmisc_1(k2_zfmisc_1(B_93, A_94))) | k2_relset_1(A_94, B_93, C_92)!=B_93 | ~v2_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))) | ~v1_funct_2(C_92, A_94, B_93) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.92  tff(c_413, plain, (![C_92, B_93, A_94]: (v1_relat_1(k2_funct_1(C_92)) | ~v1_relat_1(k2_zfmisc_1(B_93, A_94)) | k2_relset_1(A_94, B_93, C_92)!=B_93 | ~v2_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))) | ~v1_funct_2(C_92, A_94, B_93) | ~v1_funct_1(C_92))), inference(resolution, [status(thm)], [c_389, c_4])).
% 4.74/1.92  tff(c_427, plain, (![C_95, A_96, B_97]: (v1_relat_1(k2_funct_1(C_95)) | k2_relset_1(A_96, B_97, C_95)!=B_97 | ~v2_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_95, A_96, B_97) | ~v1_funct_1(C_95))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_413])).
% 4.74/1.92  tff(c_433, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_276, c_427])).
% 4.74/1.92  tff(c_437, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_278, c_62, c_277, c_433])).
% 4.74/1.92  tff(c_40, plain, (![A_25]: (k6_relat_1(A_25)=k6_partfun1(A_25))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.74/1.92  tff(c_14, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.74/1.92  tff(c_77, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 4.74/1.92  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.74/1.92  tff(c_438, plain, (![B_98, C_99, A_100]: (k6_partfun1(B_98)=k5_relat_1(k2_funct_1(C_99), C_99) | k1_xboole_0=B_98 | ~v2_funct_1(C_99) | k2_relset_1(A_100, B_98, C_99)!=B_98 | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_98))) | ~v1_funct_2(C_99, A_100, B_98) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.74/1.92  tff(c_442, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_276, c_438])).
% 4.74/1.92  tff(c_446, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_278, c_277, c_62, c_442])).
% 4.74/1.92  tff(c_447, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_446])).
% 4.74/1.92  tff(c_456, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_447, c_221])).
% 4.74/1.92  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_456])).
% 4.74/1.92  tff(c_461, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_446])).
% 4.74/1.92  tff(c_18, plain, (![B_10, A_8]: (v2_funct_1(B_10) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(k5_relat_1(B_10, A_8)) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.74/1.92  tff(c_469, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k6_partfun1(k2_relat_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_461, c_18])).
% 4.74/1.92  tff(c_475, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_70, c_437, c_362, c_77, c_469])).
% 4.74/1.92  tff(c_477, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_475])).
% 4.74/1.92  tff(c_480, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_477])).
% 4.74/1.92  tff(c_484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_70, c_62, c_480])).
% 4.74/1.92  tff(c_486, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_475])).
% 4.74/1.92  tff(c_30, plain, (![A_16, B_17, C_18]: (k2_relset_1(A_16, B_17, C_18)=k2_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.74/1.92  tff(c_676, plain, (![B_113, A_114, C_115]: (k2_relset_1(B_113, A_114, k2_funct_1(C_115))=k2_relat_1(k2_funct_1(C_115)) | k2_relset_1(A_114, B_113, C_115)!=B_113 | ~v2_funct_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))) | ~v1_funct_2(C_115, A_114, B_113) | ~v1_funct_1(C_115))), inference(resolution, [status(thm)], [c_389, c_30])).
% 4.74/1.92  tff(c_682, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_276, c_676])).
% 4.74/1.92  tff(c_686, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_278, c_62, c_277, c_486, c_682])).
% 4.74/1.92  tff(c_485, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_475])).
% 4.74/1.92  tff(c_58, plain, (![A_38, B_39, C_40]: (k2_tops_2(A_38, B_39, C_40)=k2_funct_1(C_40) | ~v2_funct_1(C_40) | k2_relset_1(A_38, B_39, C_40)!=B_39 | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_2(C_40, A_38, B_39) | ~v1_funct_1(C_40))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.74/1.92  tff(c_1207, plain, (![B_149, A_150, C_151]: (k2_tops_2(B_149, A_150, k2_funct_1(C_151))=k2_funct_1(k2_funct_1(C_151)) | ~v2_funct_1(k2_funct_1(C_151)) | k2_relset_1(B_149, A_150, k2_funct_1(C_151))!=A_150 | ~v1_funct_2(k2_funct_1(C_151), B_149, A_150) | ~v1_funct_1(k2_funct_1(C_151)) | k2_relset_1(A_150, B_149, C_151)!=B_149 | ~v2_funct_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))) | ~v1_funct_2(C_151, A_150, B_149) | ~v1_funct_1(C_151))), inference(resolution, [status(thm)], [c_389, c_58])).
% 4.74/1.92  tff(c_1213, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_276, c_1207])).
% 4.74/1.92  tff(c_1217, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_278, c_62, c_277, c_362, c_369, c_686, c_485, c_1213])).
% 4.74/1.92  tff(c_370, plain, (![A_88, B_89, C_90]: (k2_tops_2(A_88, B_89, C_90)=k2_funct_1(C_90) | ~v2_funct_1(C_90) | k2_relset_1(A_88, B_89, C_90)!=B_89 | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_2(C_90, A_88, B_89) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.74/1.92  tff(c_373, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_276, c_370])).
% 4.74/1.92  tff(c_376, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_278, c_277, c_62, c_373])).
% 4.74/1.92  tff(c_60, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.74/1.92  tff(c_148, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_99, c_98, c_98, c_98, c_60])).
% 4.74/1.92  tff(c_218, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_212, c_212, c_148])).
% 4.74/1.92  tff(c_343, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_274, c_274, c_218])).
% 4.74/1.92  tff(c_377, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_343])).
% 4.74/1.92  tff(c_1218, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1217, c_377])).
% 4.74/1.92  tff(c_1225, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1218])).
% 4.74/1.92  tff(c_1228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_70, c_62, c_709, c_1225])).
% 4.74/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.92  
% 4.74/1.92  Inference rules
% 4.74/1.92  ----------------------
% 4.74/1.92  #Ref     : 0
% 4.74/1.92  #Sup     : 244
% 4.74/1.92  #Fact    : 0
% 4.74/1.92  #Define  : 0
% 4.74/1.92  #Split   : 15
% 4.74/1.92  #Chain   : 0
% 4.74/1.92  #Close   : 0
% 4.74/1.92  
% 4.74/1.92  Ordering : KBO
% 4.74/1.92  
% 4.74/1.92  Simplification rules
% 4.74/1.92  ----------------------
% 4.74/1.92  #Subsume      : 6
% 4.74/1.92  #Demod        : 527
% 4.74/1.92  #Tautology    : 125
% 4.74/1.92  #SimpNegUnit  : 7
% 4.74/1.92  #BackRed      : 28
% 4.74/1.93  
% 4.74/1.93  #Partial instantiations: 0
% 4.74/1.93  #Strategies tried      : 1
% 4.74/1.93  
% 4.74/1.93  Timing (in seconds)
% 4.74/1.93  ----------------------
% 4.74/1.93  Preprocessing        : 0.41
% 4.74/1.93  Parsing              : 0.21
% 4.74/1.93  CNF conversion       : 0.03
% 4.74/1.93  Main loop            : 0.58
% 4.74/1.93  Inferencing          : 0.19
% 4.74/1.93  Reduction            : 0.20
% 4.74/1.93  Demodulation         : 0.15
% 4.74/1.93  BG Simplification    : 0.03
% 4.74/1.93  Subsumption          : 0.12
% 4.74/1.93  Abstraction          : 0.03
% 4.74/1.93  MUC search           : 0.00
% 4.74/1.93  Cooper               : 0.00
% 4.74/1.93  Total                : 1.07
% 4.74/1.93  Index Insertion      : 0.00
% 4.74/1.93  Index Deletion       : 0.00
% 4.74/1.93  Index Matching       : 0.00
% 4.74/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
