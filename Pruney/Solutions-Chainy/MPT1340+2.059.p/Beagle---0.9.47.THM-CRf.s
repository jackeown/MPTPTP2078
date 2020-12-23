%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:38 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :  168 (23645 expanded)
%              Number of leaves         :   46 (8224 expanded)
%              Depth                    :   26
%              Number of atoms          :  433 (67684 expanded)
%              Number of equality atoms :   87 (14632 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_201,negated_conjecture,(
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

tff(f_159,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_167,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_139,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_155,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_63,axiom,(
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

tff(f_179,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_78,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_86,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_78])).

tff(c_70,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_85,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_78])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_112,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_85,c_64])).

tff(c_118,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_112,c_118])).

tff(c_124,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_121])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_195,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_199,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_195])).

tff(c_62,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_113,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_85,c_62])).

tff(c_200,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_113])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_98,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(u1_struct_0(A_48))
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_104,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_98])).

tff(c_108,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_104])).

tff(c_109,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_108])).

tff(c_209,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_109])).

tff(c_125,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_129,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_112,c_125])).

tff(c_172,plain,(
    ! [B_61,A_62] :
      ( k1_relat_1(B_61) = A_62
      | ~ v1_partfun1(B_61,A_62)
      | ~ v4_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_175,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_172])).

tff(c_178,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_175])).

tff(c_179,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_87,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_66])).

tff(c_96,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_87])).

tff(c_210,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_96])).

tff(c_208,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_112])).

tff(c_275,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_partfun1(C_69,A_70)
      | ~ v1_funct_2(C_69,A_70,B_71)
      | ~ v1_funct_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | v1_xboole_0(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_278,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_208,c_275])).

tff(c_281,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_210,c_278])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_179,c_281])).

tff(c_284,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_289,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_112])).

tff(c_356,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_360,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_356])).

tff(c_288,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_113])).

tff(c_361,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_288])).

tff(c_291,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_96])).

tff(c_369,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_291])).

tff(c_368,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_289])).

tff(c_436,plain,(
    ! [A_78,B_79,D_80] :
      ( r2_funct_2(A_78,B_79,D_80,D_80)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(D_80,A_78,B_79)
      | ~ v1_funct_1(D_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_438,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_368,c_436])).

tff(c_441,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_369,c_438])).

tff(c_26,plain,(
    ! [A_13] :
      ( k2_funct_1(k2_funct_1(A_13)) = A_13
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_367,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_360])).

tff(c_486,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_funct_1(k2_funct_1(C_90))
      | k2_relset_1(A_91,B_92,C_90) != B_92
      | ~ v2_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_2(C_90,A_91,B_92)
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_489,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_368,c_486])).

tff(c_492,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_369,c_60,c_367,c_489])).

tff(c_572,plain,(
    ! [C_97,B_98,A_99] :
      ( v1_funct_2(k2_funct_1(C_97),B_98,A_99)
      | k2_relset_1(A_99,B_98,C_97) != B_98
      | ~ v2_funct_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98)))
      | ~ v1_funct_2(C_97,A_99,B_98)
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_575,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_368,c_572])).

tff(c_578,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_369,c_60,c_367,c_575])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_673,plain,(
    ! [C_107,B_108,A_109] :
      ( m1_subset_1(k2_funct_1(C_107),k1_zfmisc_1(k2_zfmisc_1(B_108,A_109)))
      | k2_relset_1(A_109,B_108,C_107) != B_108
      | ~ v2_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108)))
      | ~ v1_funct_2(C_107,A_109,B_108)
      | ~ v1_funct_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_699,plain,(
    ! [C_107,B_108,A_109] :
      ( v1_relat_1(k2_funct_1(C_107))
      | ~ v1_relat_1(k2_zfmisc_1(B_108,A_109))
      | k2_relset_1(A_109,B_108,C_107) != B_108
      | ~ v2_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108)))
      | ~ v1_funct_2(C_107,A_109,B_108)
      | ~ v1_funct_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_673,c_2])).

tff(c_721,plain,(
    ! [C_114,A_115,B_116] :
      ( v1_relat_1(k2_funct_1(C_114))
      | k2_relset_1(A_115,B_116,C_114) != B_116
      | ~ v2_funct_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_2(C_114,A_115,B_116)
      | ~ v1_funct_1(C_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_699])).

tff(c_727,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_368,c_721])).

tff(c_731,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_369,c_60,c_367,c_727])).

tff(c_30,plain,(
    ! [C_16,A_14,B_15] :
      ( v4_relat_1(C_16,A_14)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_732,plain,(
    ! [C_117,B_118,A_119] :
      ( v4_relat_1(k2_funct_1(C_117),B_118)
      | k2_relset_1(A_119,B_118,C_117) != B_118
      | ~ v2_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118)))
      | ~ v1_funct_2(C_117,A_119,B_118)
      | ~ v1_funct_1(C_117) ) ),
    inference(resolution,[status(thm)],[c_673,c_30])).

tff(c_738,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_368,c_732])).

tff(c_742,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_369,c_60,c_367,c_738])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_337,plain,(
    ! [A_72] :
      ( k1_relat_1(k2_funct_1(A_72)) = k2_relat_1(A_72)
      | ~ v2_funct_1(A_72)
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    ! [B_25] :
      ( v1_partfun1(B_25,k1_relat_1(B_25))
      | ~ v4_relat_1(B_25,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_476,plain,(
    ! [A_89] :
      ( v1_partfun1(k2_funct_1(A_89),k1_relat_1(k2_funct_1(A_89)))
      | ~ v4_relat_1(k2_funct_1(A_89),k2_relat_1(A_89))
      | ~ v1_relat_1(k2_funct_1(A_89))
      | ~ v2_funct_1(A_89)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_38])).

tff(c_479,plain,(
    ! [A_11] :
      ( v1_partfun1(k2_funct_1(A_11),k2_relat_1(A_11))
      | ~ v4_relat_1(k2_funct_1(A_11),k2_relat_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_476])).

tff(c_745,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_742,c_479])).

tff(c_751,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_68,c_60,c_731,c_745])).

tff(c_40,plain,(
    ! [B_25,A_24] :
      ( k1_relat_1(B_25) = A_24
      | ~ v1_partfun1(B_25,A_24)
      | ~ v4_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_748,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_742,c_40])).

tff(c_754,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_748])).

tff(c_756,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_754])).

tff(c_12,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_relat_1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_450,plain,(
    ! [A_84,B_85] :
      ( v2_funct_1(A_84)
      | k2_relat_1(B_85) != k1_relat_1(A_84)
      | ~ v2_funct_1(k5_relat_1(B_85,A_84))
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_456,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | k1_relat_1(k2_funct_1(A_12)) != k2_relat_1(A_12)
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(A_12)))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12)
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_450])).

tff(c_460,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | k1_relat_1(k2_funct_1(A_12)) != k2_relat_1(A_12)
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_456])).

tff(c_387,plain,(
    ! [A_76] :
      ( k5_relat_1(A_76,k2_funct_1(A_76)) = k6_relat_1(k1_relat_1(A_76))
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_396,plain,(
    ! [A_13] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(A_13))) = k5_relat_1(k2_funct_1(A_13),A_13)
      | ~ v2_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_387])).

tff(c_760,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_396])).

tff(c_776,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_68,c_60,c_731,c_492,c_760])).

tff(c_788,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_776])).

tff(c_791,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_460,c_788])).

tff(c_798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_68,c_60,c_731,c_492,c_756,c_791])).

tff(c_800,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_776])).

tff(c_32,plain,(
    ! [A_17,B_18,C_19] :
      ( k2_relset_1(A_17,B_18,C_19) = k2_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_848,plain,(
    ! [B_123,A_124,C_125] :
      ( k2_relset_1(B_123,A_124,k2_funct_1(C_125)) = k2_relat_1(k2_funct_1(C_125))
      | k2_relset_1(A_124,B_123,C_125) != B_123
      | ~ v2_funct_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123)))
      | ~ v1_funct_2(C_125,A_124,B_123)
      | ~ v1_funct_1(C_125) ) ),
    inference(resolution,[status(thm)],[c_673,c_32])).

tff(c_854,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_368,c_848])).

tff(c_858,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_369,c_60,c_367,c_854])).

tff(c_50,plain,(
    ! [C_32,A_30,B_31] :
      ( v1_funct_1(k2_funct_1(C_32))
      | k2_relset_1(A_30,B_31,C_32) != B_31
      | ~ v2_funct_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ v1_funct_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1145,plain,(
    ! [C_143,B_144,A_145] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_143)))
      | k2_relset_1(B_144,A_145,k2_funct_1(C_143)) != A_145
      | ~ v2_funct_1(k2_funct_1(C_143))
      | ~ v1_funct_2(k2_funct_1(C_143),B_144,A_145)
      | ~ v1_funct_1(k2_funct_1(C_143))
      | k2_relset_1(A_145,B_144,C_143) != B_144
      | ~ v2_funct_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144)))
      | ~ v1_funct_2(C_143,A_145,B_144)
      | ~ v1_funct_1(C_143) ) ),
    inference(resolution,[status(thm)],[c_673,c_50])).

tff(c_1151,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_368,c_1145])).

tff(c_1155,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_369,c_60,c_367,c_492,c_578,c_800,c_858,c_1151])).

tff(c_1156,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1155])).

tff(c_1159,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1156])).

tff(c_1163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_68,c_60,c_1159])).

tff(c_1165,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1155])).

tff(c_1171,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1165,c_858])).

tff(c_56,plain,(
    ! [A_35,B_36,C_37] :
      ( k2_tops_2(A_35,B_36,C_37) = k2_funct_1(C_37)
      | ~ v2_funct_1(C_37)
      | k2_relset_1(A_35,B_36,C_37) != B_36
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_2(C_37,A_35,B_36)
      | ~ v1_funct_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1332,plain,(
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
    inference(resolution,[status(thm)],[c_673,c_56])).

tff(c_1338,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_368,c_1332])).

tff(c_1342,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_369,c_60,c_367,c_492,c_578,c_1171,c_800,c_1338])).

tff(c_642,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_tops_2(A_102,B_103,C_104) = k2_funct_1(C_104)
      | ~ v2_funct_1(C_104)
      | k2_relset_1(A_102,B_103,C_104) != B_103
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ v1_funct_2(C_104,A_102,B_103)
      | ~ v1_funct_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_645,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_368,c_642])).

tff(c_648,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_369,c_367,c_60,c_645])).

tff(c_58,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_159,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_86,c_85,c_85,c_85,c_58])).

tff(c_286,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_284,c_284,c_159])).

tff(c_366,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_361,c_361,c_286])).

tff(c_649,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_366])).

tff(c_1343,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1342,c_649])).

tff(c_1350,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1343])).

tff(c_1353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_68,c_60,c_441,c_1350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.80  
% 4.26/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.80  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.26/1.80  
% 4.26/1.80  %Foreground sorts:
% 4.26/1.80  
% 4.26/1.80  
% 4.26/1.80  %Background operators:
% 4.26/1.80  
% 4.26/1.80  
% 4.26/1.80  %Foreground operators:
% 4.26/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.26/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.26/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.26/1.80  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.26/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.26/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.80  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.26/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.26/1.80  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.26/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.26/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.26/1.80  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.26/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.26/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.26/1.80  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.26/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.26/1.80  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.26/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.26/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.26/1.80  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.26/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.26/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.26/1.80  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.26/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.26/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.26/1.80  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.26/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.26/1.80  
% 4.66/1.83  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.66/1.83  tff(f_201, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 4.66/1.83  tff(f_159, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.66/1.83  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.66/1.83  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.66/1.83  tff(f_167, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.66/1.83  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.66/1.83  tff(f_123, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.66/1.83  tff(f_115, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.66/1.83  tff(f_139, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 4.66/1.83  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 4.66/1.83  tff(f_155, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.66/1.83  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.66/1.83  tff(f_46, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.66/1.83  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.66/1.83  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 4.66/1.83  tff(f_179, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 4.66/1.83  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.66/1.83  tff(c_74, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.66/1.83  tff(c_78, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.66/1.83  tff(c_86, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_78])).
% 4.66/1.83  tff(c_70, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.66/1.83  tff(c_85, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_78])).
% 4.66/1.83  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.66/1.83  tff(c_112, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_85, c_64])).
% 4.66/1.83  tff(c_118, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.66/1.83  tff(c_121, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_112, c_118])).
% 4.66/1.83  tff(c_124, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_121])).
% 4.66/1.83  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.66/1.83  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.66/1.83  tff(c_195, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.66/1.83  tff(c_199, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_195])).
% 4.66/1.83  tff(c_62, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.66/1.83  tff(c_113, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_85, c_62])).
% 4.66/1.83  tff(c_200, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_113])).
% 4.66/1.83  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.66/1.83  tff(c_98, plain, (![A_48]: (~v1_xboole_0(u1_struct_0(A_48)) | ~l1_struct_0(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.66/1.83  tff(c_104, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_98])).
% 4.66/1.83  tff(c_108, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_104])).
% 4.66/1.83  tff(c_109, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_108])).
% 4.66/1.83  tff(c_209, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_109])).
% 4.66/1.83  tff(c_125, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.66/1.83  tff(c_129, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_112, c_125])).
% 4.66/1.83  tff(c_172, plain, (![B_61, A_62]: (k1_relat_1(B_61)=A_62 | ~v1_partfun1(B_61, A_62) | ~v4_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.83  tff(c_175, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_172])).
% 4.66/1.83  tff(c_178, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_175])).
% 4.66/1.83  tff(c_179, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_178])).
% 4.66/1.83  tff(c_66, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.66/1.83  tff(c_87, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_66])).
% 4.66/1.83  tff(c_96, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_87])).
% 4.66/1.83  tff(c_210, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_96])).
% 4.66/1.83  tff(c_208, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_112])).
% 4.66/1.83  tff(c_275, plain, (![C_69, A_70, B_71]: (v1_partfun1(C_69, A_70) | ~v1_funct_2(C_69, A_70, B_71) | ~v1_funct_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | v1_xboole_0(B_71))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.66/1.83  tff(c_278, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_208, c_275])).
% 4.66/1.83  tff(c_281, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_210, c_278])).
% 4.66/1.83  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_179, c_281])).
% 4.66/1.83  tff(c_284, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_178])).
% 4.66/1.83  tff(c_289, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_112])).
% 4.66/1.83  tff(c_356, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.66/1.83  tff(c_360, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_356])).
% 4.66/1.83  tff(c_288, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_113])).
% 4.66/1.83  tff(c_361, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_288])).
% 4.66/1.83  tff(c_291, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_96])).
% 4.66/1.83  tff(c_369, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_291])).
% 4.66/1.83  tff(c_368, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_289])).
% 4.66/1.83  tff(c_436, plain, (![A_78, B_79, D_80]: (r2_funct_2(A_78, B_79, D_80, D_80) | ~m1_subset_1(D_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(D_80, A_78, B_79) | ~v1_funct_1(D_80))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.66/1.83  tff(c_438, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_368, c_436])).
% 4.66/1.83  tff(c_441, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_369, c_438])).
% 4.66/1.83  tff(c_26, plain, (![A_13]: (k2_funct_1(k2_funct_1(A_13))=A_13 | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.66/1.83  tff(c_367, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_361, c_360])).
% 4.66/1.83  tff(c_486, plain, (![C_90, A_91, B_92]: (v1_funct_1(k2_funct_1(C_90)) | k2_relset_1(A_91, B_92, C_90)!=B_92 | ~v2_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.66/1.83  tff(c_489, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_368, c_486])).
% 4.66/1.83  tff(c_492, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_369, c_60, c_367, c_489])).
% 4.66/1.83  tff(c_572, plain, (![C_97, B_98, A_99]: (v1_funct_2(k2_funct_1(C_97), B_98, A_99) | k2_relset_1(A_99, B_98, C_97)!=B_98 | ~v2_funct_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))) | ~v1_funct_2(C_97, A_99, B_98) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.66/1.83  tff(c_575, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_368, c_572])).
% 4.66/1.83  tff(c_578, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_369, c_60, c_367, c_575])).
% 4.66/1.83  tff(c_18, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.66/1.83  tff(c_673, plain, (![C_107, B_108, A_109]: (m1_subset_1(k2_funct_1(C_107), k1_zfmisc_1(k2_zfmisc_1(B_108, A_109))) | k2_relset_1(A_109, B_108, C_107)!=B_108 | ~v2_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))) | ~v1_funct_2(C_107, A_109, B_108) | ~v1_funct_1(C_107))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.66/1.83  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.66/1.83  tff(c_699, plain, (![C_107, B_108, A_109]: (v1_relat_1(k2_funct_1(C_107)) | ~v1_relat_1(k2_zfmisc_1(B_108, A_109)) | k2_relset_1(A_109, B_108, C_107)!=B_108 | ~v2_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))) | ~v1_funct_2(C_107, A_109, B_108) | ~v1_funct_1(C_107))), inference(resolution, [status(thm)], [c_673, c_2])).
% 4.66/1.83  tff(c_721, plain, (![C_114, A_115, B_116]: (v1_relat_1(k2_funct_1(C_114)) | k2_relset_1(A_115, B_116, C_114)!=B_116 | ~v2_funct_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_2(C_114, A_115, B_116) | ~v1_funct_1(C_114))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_699])).
% 4.66/1.83  tff(c_727, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_368, c_721])).
% 4.66/1.83  tff(c_731, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_369, c_60, c_367, c_727])).
% 4.66/1.83  tff(c_30, plain, (![C_16, A_14, B_15]: (v4_relat_1(C_16, A_14) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.66/1.83  tff(c_732, plain, (![C_117, B_118, A_119]: (v4_relat_1(k2_funct_1(C_117), B_118) | k2_relset_1(A_119, B_118, C_117)!=B_118 | ~v2_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))) | ~v1_funct_2(C_117, A_119, B_118) | ~v1_funct_1(C_117))), inference(resolution, [status(thm)], [c_673, c_30])).
% 4.66/1.83  tff(c_738, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_368, c_732])).
% 4.66/1.83  tff(c_742, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_369, c_60, c_367, c_738])).
% 4.66/1.83  tff(c_20, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.66/1.83  tff(c_337, plain, (![A_72]: (k1_relat_1(k2_funct_1(A_72))=k2_relat_1(A_72) | ~v2_funct_1(A_72) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.66/1.83  tff(c_38, plain, (![B_25]: (v1_partfun1(B_25, k1_relat_1(B_25)) | ~v4_relat_1(B_25, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.83  tff(c_476, plain, (![A_89]: (v1_partfun1(k2_funct_1(A_89), k1_relat_1(k2_funct_1(A_89))) | ~v4_relat_1(k2_funct_1(A_89), k2_relat_1(A_89)) | ~v1_relat_1(k2_funct_1(A_89)) | ~v2_funct_1(A_89) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(superposition, [status(thm), theory('equality')], [c_337, c_38])).
% 4.66/1.83  tff(c_479, plain, (![A_11]: (v1_partfun1(k2_funct_1(A_11), k2_relat_1(A_11)) | ~v4_relat_1(k2_funct_1(A_11), k2_relat_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_20, c_476])).
% 4.66/1.83  tff(c_745, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_742, c_479])).
% 4.66/1.83  tff(c_751, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_68, c_60, c_731, c_745])).
% 4.66/1.83  tff(c_40, plain, (![B_25, A_24]: (k1_relat_1(B_25)=A_24 | ~v1_partfun1(B_25, A_24) | ~v4_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.83  tff(c_748, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_742, c_40])).
% 4.66/1.83  tff(c_754, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_748])).
% 4.66/1.83  tff(c_756, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_751, c_754])).
% 4.66/1.83  tff(c_12, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.66/1.83  tff(c_24, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_relat_1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.66/1.83  tff(c_450, plain, (![A_84, B_85]: (v2_funct_1(A_84) | k2_relat_1(B_85)!=k1_relat_1(A_84) | ~v2_funct_1(k5_relat_1(B_85, A_84)) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.66/1.83  tff(c_456, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | k1_relat_1(k2_funct_1(A_12))!=k2_relat_1(A_12) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_12))) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_24, c_450])).
% 4.66/1.83  tff(c_460, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | k1_relat_1(k2_funct_1(A_12))!=k2_relat_1(A_12) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_456])).
% 4.66/1.83  tff(c_387, plain, (![A_76]: (k5_relat_1(A_76, k2_funct_1(A_76))=k6_relat_1(k1_relat_1(A_76)) | ~v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.66/1.83  tff(c_396, plain, (![A_13]: (k6_relat_1(k1_relat_1(k2_funct_1(A_13)))=k5_relat_1(k2_funct_1(A_13), A_13) | ~v2_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_26, c_387])).
% 4.66/1.83  tff(c_760, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_756, c_396])).
% 4.66/1.83  tff(c_776, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_68, c_60, c_731, c_492, c_760])).
% 4.66/1.83  tff(c_788, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_776])).
% 4.66/1.83  tff(c_791, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_460, c_788])).
% 4.66/1.83  tff(c_798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_68, c_60, c_731, c_492, c_756, c_791])).
% 4.66/1.83  tff(c_800, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_776])).
% 4.66/1.83  tff(c_32, plain, (![A_17, B_18, C_19]: (k2_relset_1(A_17, B_18, C_19)=k2_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.66/1.83  tff(c_848, plain, (![B_123, A_124, C_125]: (k2_relset_1(B_123, A_124, k2_funct_1(C_125))=k2_relat_1(k2_funct_1(C_125)) | k2_relset_1(A_124, B_123, C_125)!=B_123 | ~v2_funct_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))) | ~v1_funct_2(C_125, A_124, B_123) | ~v1_funct_1(C_125))), inference(resolution, [status(thm)], [c_673, c_32])).
% 4.66/1.83  tff(c_854, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_368, c_848])).
% 4.66/1.83  tff(c_858, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_369, c_60, c_367, c_854])).
% 4.66/1.83  tff(c_50, plain, (![C_32, A_30, B_31]: (v1_funct_1(k2_funct_1(C_32)) | k2_relset_1(A_30, B_31, C_32)!=B_31 | ~v2_funct_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(C_32, A_30, B_31) | ~v1_funct_1(C_32))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.66/1.83  tff(c_1145, plain, (![C_143, B_144, A_145]: (v1_funct_1(k2_funct_1(k2_funct_1(C_143))) | k2_relset_1(B_144, A_145, k2_funct_1(C_143))!=A_145 | ~v2_funct_1(k2_funct_1(C_143)) | ~v1_funct_2(k2_funct_1(C_143), B_144, A_145) | ~v1_funct_1(k2_funct_1(C_143)) | k2_relset_1(A_145, B_144, C_143)!=B_144 | ~v2_funct_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))) | ~v1_funct_2(C_143, A_145, B_144) | ~v1_funct_1(C_143))), inference(resolution, [status(thm)], [c_673, c_50])).
% 4.66/1.83  tff(c_1151, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_368, c_1145])).
% 4.66/1.83  tff(c_1155, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_369, c_60, c_367, c_492, c_578, c_800, c_858, c_1151])).
% 4.66/1.83  tff(c_1156, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1155])).
% 4.66/1.83  tff(c_1159, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1156])).
% 4.66/1.83  tff(c_1163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_68, c_60, c_1159])).
% 4.66/1.83  tff(c_1165, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1155])).
% 4.66/1.83  tff(c_1171, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1165, c_858])).
% 4.66/1.83  tff(c_56, plain, (![A_35, B_36, C_37]: (k2_tops_2(A_35, B_36, C_37)=k2_funct_1(C_37) | ~v2_funct_1(C_37) | k2_relset_1(A_35, B_36, C_37)!=B_36 | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_2(C_37, A_35, B_36) | ~v1_funct_1(C_37))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.66/1.83  tff(c_1332, plain, (![B_149, A_150, C_151]: (k2_tops_2(B_149, A_150, k2_funct_1(C_151))=k2_funct_1(k2_funct_1(C_151)) | ~v2_funct_1(k2_funct_1(C_151)) | k2_relset_1(B_149, A_150, k2_funct_1(C_151))!=A_150 | ~v1_funct_2(k2_funct_1(C_151), B_149, A_150) | ~v1_funct_1(k2_funct_1(C_151)) | k2_relset_1(A_150, B_149, C_151)!=B_149 | ~v2_funct_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))) | ~v1_funct_2(C_151, A_150, B_149) | ~v1_funct_1(C_151))), inference(resolution, [status(thm)], [c_673, c_56])).
% 4.66/1.83  tff(c_1338, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_368, c_1332])).
% 4.66/1.83  tff(c_1342, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_369, c_60, c_367, c_492, c_578, c_1171, c_800, c_1338])).
% 4.66/1.83  tff(c_642, plain, (![A_102, B_103, C_104]: (k2_tops_2(A_102, B_103, C_104)=k2_funct_1(C_104) | ~v2_funct_1(C_104) | k2_relset_1(A_102, B_103, C_104)!=B_103 | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~v1_funct_2(C_104, A_102, B_103) | ~v1_funct_1(C_104))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.66/1.83  tff(c_645, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_368, c_642])).
% 4.66/1.83  tff(c_648, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_369, c_367, c_60, c_645])).
% 4.66/1.83  tff(c_58, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.66/1.83  tff(c_159, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_86, c_86, c_85, c_85, c_85, c_58])).
% 4.66/1.83  tff(c_286, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_284, c_284, c_159])).
% 4.66/1.83  tff(c_366, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_361, c_361, c_361, c_286])).
% 4.66/1.83  tff(c_649, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_648, c_366])).
% 4.66/1.83  tff(c_1343, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1342, c_649])).
% 4.66/1.83  tff(c_1350, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1343])).
% 4.66/1.83  tff(c_1353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_68, c_60, c_441, c_1350])).
% 4.66/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.83  
% 4.66/1.83  Inference rules
% 4.66/1.83  ----------------------
% 4.66/1.83  #Ref     : 0
% 4.66/1.83  #Sup     : 302
% 4.66/1.83  #Fact    : 0
% 4.66/1.83  #Define  : 0
% 4.66/1.83  #Split   : 7
% 4.66/1.83  #Chain   : 0
% 4.66/1.83  #Close   : 0
% 4.66/1.83  
% 4.66/1.83  Ordering : KBO
% 4.66/1.83  
% 4.66/1.83  Simplification rules
% 4.66/1.83  ----------------------
% 4.66/1.83  #Subsume      : 42
% 4.66/1.83  #Demod        : 362
% 4.66/1.83  #Tautology    : 161
% 4.66/1.83  #SimpNegUnit  : 6
% 4.66/1.83  #BackRed      : 27
% 4.66/1.83  
% 4.66/1.83  #Partial instantiations: 0
% 4.66/1.83  #Strategies tried      : 1
% 4.66/1.83  
% 4.66/1.83  Timing (in seconds)
% 4.66/1.83  ----------------------
% 4.66/1.83  Preprocessing        : 0.40
% 4.66/1.83  Parsing              : 0.22
% 4.66/1.83  CNF conversion       : 0.03
% 4.66/1.83  Main loop            : 0.57
% 4.66/1.83  Inferencing          : 0.20
% 4.66/1.83  Reduction            : 0.21
% 4.66/1.83  Demodulation         : 0.16
% 4.66/1.83  BG Simplification    : 0.03
% 4.66/1.83  Subsumption          : 0.09
% 4.66/1.83  Abstraction          : 0.03
% 4.66/1.83  MUC search           : 0.00
% 4.66/1.83  Cooper               : 0.00
% 4.66/1.83  Total                : 1.02
% 4.66/1.83  Index Insertion      : 0.00
% 4.66/1.83  Index Deletion       : 0.00
% 4.66/1.83  Index Matching       : 0.00
% 4.66/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
