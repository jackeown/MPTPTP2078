%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:22 EST 2020

% Result     : Theorem 5.49s
% Output     : CNFRefutation 5.49s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 275 expanded)
%              Number of leaves         :   42 ( 115 expanded)
%              Depth                    :   11
%              Number of atoms          :  243 (1067 expanded)
%              Number of equality atoms :  102 ( 388 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_165,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_123,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_139,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_142,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_155,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_142])).

tff(c_235,plain,(
    ! [B_76,A_77,C_78] :
      ( k1_xboole_0 = B_76
      | k1_relset_1(A_77,B_76,C_78) = A_77
      | ~ v1_funct_2(C_78,A_77,B_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_244,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_235])).

tff(c_253,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_155,c_244])).

tff(c_254,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_253])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_112,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_112])).

tff(c_130,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_121])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_118,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_112])).

tff(c_127,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_118])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_154,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_142])).

tff(c_241,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_235])).

tff(c_249,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_154,c_241])).

tff(c_250,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_249])).

tff(c_44,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_relat_1(k1_relat_1(A_8)) != k5_relat_1(A_8,B_10)
      | k2_relat_1(A_8) != k1_relat_1(B_10)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_377,plain,(
    ! [A_101,B_102] :
      ( k2_funct_1(A_101) = B_102
      | k6_partfun1(k1_relat_1(A_101)) != k5_relat_1(A_101,B_102)
      | k2_relat_1(A_101) != k1_relat_1(B_102)
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(B_102)
      | ~ v1_relat_1(B_102)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_14])).

tff(c_381,plain,(
    ! [B_102] :
      ( k2_funct_1('#skF_3') = B_102
      | k5_relat_1('#skF_3',B_102) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_102)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_102)
      | ~ v1_relat_1(B_102)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_377])).

tff(c_2224,plain,(
    ! [B_182] :
      ( k2_funct_1('#skF_3') = B_182
      | k5_relat_1('#skF_3',B_182) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_182)
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_56,c_381])).

tff(c_2230,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_2224])).

tff(c_2241,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_254,c_2230])).

tff(c_2242,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2241])).

tff(c_2247,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2242])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_2717,plain,(
    ! [B_202,C_203,A_204] :
      ( k6_partfun1(B_202) = k5_relat_1(k2_funct_1(C_203),C_203)
      | k1_xboole_0 = B_202
      | ~ v2_funct_1(C_203)
      | k2_relset_1(A_204,B_202,C_203) != B_202
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_204,B_202)))
      | ~ v1_funct_2(C_203,A_204,B_202)
      | ~ v1_funct_1(C_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2737,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2717])).

tff(c_2762,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_2737])).

tff(c_2763,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2762])).

tff(c_10,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_2771,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2763,c_75])).

tff(c_2778,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_56,c_2771])).

tff(c_2838,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2778,c_77])).

tff(c_2861,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2838])).

tff(c_2863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2247,c_2861])).

tff(c_2864,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2242])).

tff(c_297,plain,(
    ! [A_87,D_85,B_84,F_88,C_83,E_86] :
      ( k4_relset_1(A_87,B_84,C_83,D_85,E_86,F_88) = k5_relat_1(E_86,F_88)
      | ~ m1_subset_1(F_88,k1_zfmisc_1(k2_zfmisc_1(C_83,D_85)))
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_328,plain,(
    ! [A_92,B_93,E_94] :
      ( k4_relset_1(A_92,B_93,'#skF_2','#skF_1',E_94,'#skF_4') = k5_relat_1(E_94,'#skF_4')
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(resolution,[status(thm)],[c_62,c_297])).

tff(c_339,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_328])).

tff(c_1244,plain,(
    ! [C_137,A_138,E_141,B_139,F_136,D_140] :
      ( m1_subset_1(k4_relset_1(A_138,B_139,C_137,D_140,E_141,F_136),k1_zfmisc_1(k2_zfmisc_1(A_138,D_140)))
      | ~ m1_subset_1(F_136,k1_zfmisc_1(k2_zfmisc_1(C_137,D_140)))
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1301,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_1244])).

tff(c_1335,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_1301])).

tff(c_1509,plain,(
    ! [C_147,E_145,A_142,D_143,B_146,F_144] :
      ( k1_partfun1(A_142,B_146,C_147,D_143,E_145,F_144) = k5_relat_1(E_145,F_144)
      | ~ m1_subset_1(F_144,k1_zfmisc_1(k2_zfmisc_1(C_147,D_143)))
      | ~ v1_funct_1(F_144)
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_142,B_146)))
      | ~ v1_funct_1(E_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1525,plain,(
    ! [A_142,B_146,E_145] :
      ( k1_partfun1(A_142,B_146,'#skF_2','#skF_1',E_145,'#skF_4') = k5_relat_1(E_145,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_142,B_146)))
      | ~ v1_funct_1(E_145) ) ),
    inference(resolution,[status(thm)],[c_62,c_1509])).

tff(c_2153,plain,(
    ! [A_179,B_180,E_181] :
      ( k1_partfun1(A_179,B_180,'#skF_2','#skF_1',E_181,'#skF_4') = k5_relat_1(E_181,'#skF_4')
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_1(E_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1525])).

tff(c_2189,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2153])).

tff(c_2206,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2189])).

tff(c_40,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_273,plain,(
    ! [D_79,C_80,A_81,B_82] :
      ( D_79 = C_80
      | ~ r2_relset_1(A_81,B_82,C_80,D_79)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_281,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_273])).

tff(c_296,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_281])).

tff(c_423,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_2210,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2206,c_423])).

tff(c_2214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1335,c_2210])).

tff(c_2215,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_3164,plain,(
    ! [E_216,A_213,D_214,B_217,C_218,F_215] :
      ( k1_partfun1(A_213,B_217,C_218,D_214,E_216,F_215) = k5_relat_1(E_216,F_215)
      | ~ m1_subset_1(F_215,k1_zfmisc_1(k2_zfmisc_1(C_218,D_214)))
      | ~ v1_funct_1(F_215)
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_213,B_217)))
      | ~ v1_funct_1(E_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3180,plain,(
    ! [A_213,B_217,E_216] :
      ( k1_partfun1(A_213,B_217,'#skF_2','#skF_1',E_216,'#skF_4') = k5_relat_1(E_216,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_213,B_217)))
      | ~ v1_funct_1(E_216) ) ),
    inference(resolution,[status(thm)],[c_62,c_3164])).

tff(c_3808,plain,(
    ! [A_250,B_251,E_252] :
      ( k1_partfun1(A_250,B_251,'#skF_2','#skF_1',E_252,'#skF_4') = k5_relat_1(E_252,'#skF_4')
      | ~ m1_subset_1(E_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251)))
      | ~ v1_funct_1(E_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3180])).

tff(c_3844,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3808])).

tff(c_3861,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2215,c_3844])).

tff(c_3863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2864,c_3861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n019.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 19:54:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.49/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/1.99  
% 5.49/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/1.99  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.49/1.99  
% 5.49/1.99  %Foreground sorts:
% 5.49/1.99  
% 5.49/1.99  
% 5.49/1.99  %Background operators:
% 5.49/1.99  
% 5.49/1.99  
% 5.49/1.99  %Foreground operators:
% 5.49/1.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.49/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.49/1.99  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.49/1.99  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.49/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.49/1.99  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.49/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.49/1.99  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.49/1.99  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.49/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.49/1.99  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.49/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.49/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.49/1.99  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.49/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.49/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.49/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.49/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.49/1.99  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.49/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.49/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.49/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.49/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.49/1.99  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.49/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.49/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.49/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.49/1.99  
% 5.49/2.01  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 5.49/2.01  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.49/2.01  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.49/2.01  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.49/2.01  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.49/2.01  tff(f_123, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.49/2.01  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 5.49/2.01  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.49/2.01  tff(f_139, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 5.49/2.01  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.49/2.01  tff(f_81, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 5.49/2.01  tff(f_71, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 5.49/2.01  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.49/2.01  tff(f_111, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.49/2.01  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.49/2.01  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_142, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.49/2.01  tff(c_155, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_142])).
% 5.49/2.01  tff(c_235, plain, (![B_76, A_77, C_78]: (k1_xboole_0=B_76 | k1_relset_1(A_77, B_76, C_78)=A_77 | ~v1_funct_2(C_78, A_77, B_76) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.49/2.01  tff(c_244, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_235])).
% 5.49/2.01  tff(c_253, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_155, c_244])).
% 5.49/2.01  tff(c_254, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_253])).
% 5.49/2.01  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.49/2.01  tff(c_112, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.49/2.01  tff(c_121, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_112])).
% 5.49/2.01  tff(c_130, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_121])).
% 5.49/2.01  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_118, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_112])).
% 5.49/2.01  tff(c_127, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_118])).
% 5.49/2.01  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_154, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_142])).
% 5.49/2.01  tff(c_241, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_235])).
% 5.49/2.01  tff(c_249, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_154, c_241])).
% 5.49/2.01  tff(c_250, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_249])).
% 5.49/2.01  tff(c_44, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.49/2.01  tff(c_14, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_relat_1(k1_relat_1(A_8))!=k5_relat_1(A_8, B_10) | k2_relat_1(A_8)!=k1_relat_1(B_10) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.49/2.01  tff(c_377, plain, (![A_101, B_102]: (k2_funct_1(A_101)=B_102 | k6_partfun1(k1_relat_1(A_101))!=k5_relat_1(A_101, B_102) | k2_relat_1(A_101)!=k1_relat_1(B_102) | ~v2_funct_1(A_101) | ~v1_funct_1(B_102) | ~v1_relat_1(B_102) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_14])).
% 5.49/2.01  tff(c_381, plain, (![B_102]: (k2_funct_1('#skF_3')=B_102 | k5_relat_1('#skF_3', B_102)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_102) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_102) | ~v1_relat_1(B_102) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_250, c_377])).
% 5.49/2.01  tff(c_2224, plain, (![B_182]: (k2_funct_1('#skF_3')=B_182 | k5_relat_1('#skF_3', B_182)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_182) | ~v1_funct_1(B_182) | ~v1_relat_1(B_182))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_56, c_381])).
% 5.49/2.01  tff(c_2230, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_130, c_2224])).
% 5.49/2.01  tff(c_2241, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_254, c_2230])).
% 5.49/2.01  tff(c_2242, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_2241])).
% 5.49/2.01  tff(c_2247, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_2242])).
% 5.49/2.01  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.49/2.01  tff(c_77, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 5.49/2.01  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_2717, plain, (![B_202, C_203, A_204]: (k6_partfun1(B_202)=k5_relat_1(k2_funct_1(C_203), C_203) | k1_xboole_0=B_202 | ~v2_funct_1(C_203) | k2_relset_1(A_204, B_202, C_203)!=B_202 | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_204, B_202))) | ~v1_funct_2(C_203, A_204, B_202) | ~v1_funct_1(C_203))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.49/2.01  tff(c_2737, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2717])).
% 5.49/2.01  tff(c_2762, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_2737])).
% 5.49/2.01  tff(c_2763, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_2762])).
% 5.49/2.01  tff(c_10, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.49/2.01  tff(c_75, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 5.49/2.01  tff(c_2771, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2763, c_75])).
% 5.49/2.01  tff(c_2778, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_56, c_2771])).
% 5.49/2.01  tff(c_2838, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2778, c_77])).
% 5.49/2.01  tff(c_2861, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2838])).
% 5.49/2.01  tff(c_2863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2247, c_2861])).
% 5.49/2.01  tff(c_2864, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2242])).
% 5.49/2.01  tff(c_297, plain, (![A_87, D_85, B_84, F_88, C_83, E_86]: (k4_relset_1(A_87, B_84, C_83, D_85, E_86, F_88)=k5_relat_1(E_86, F_88) | ~m1_subset_1(F_88, k1_zfmisc_1(k2_zfmisc_1(C_83, D_85))) | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_84))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.49/2.01  tff(c_328, plain, (![A_92, B_93, E_94]: (k4_relset_1(A_92, B_93, '#skF_2', '#skF_1', E_94, '#skF_4')=k5_relat_1(E_94, '#skF_4') | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(resolution, [status(thm)], [c_62, c_297])).
% 5.49/2.01  tff(c_339, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_328])).
% 5.49/2.01  tff(c_1244, plain, (![C_137, A_138, E_141, B_139, F_136, D_140]: (m1_subset_1(k4_relset_1(A_138, B_139, C_137, D_140, E_141, F_136), k1_zfmisc_1(k2_zfmisc_1(A_138, D_140))) | ~m1_subset_1(F_136, k1_zfmisc_1(k2_zfmisc_1(C_137, D_140))) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.49/2.01  tff(c_1301, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_339, c_1244])).
% 5.49/2.01  tff(c_1335, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_1301])).
% 5.49/2.01  tff(c_1509, plain, (![C_147, E_145, A_142, D_143, B_146, F_144]: (k1_partfun1(A_142, B_146, C_147, D_143, E_145, F_144)=k5_relat_1(E_145, F_144) | ~m1_subset_1(F_144, k1_zfmisc_1(k2_zfmisc_1(C_147, D_143))) | ~v1_funct_1(F_144) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_142, B_146))) | ~v1_funct_1(E_145))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.49/2.01  tff(c_1525, plain, (![A_142, B_146, E_145]: (k1_partfun1(A_142, B_146, '#skF_2', '#skF_1', E_145, '#skF_4')=k5_relat_1(E_145, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_142, B_146))) | ~v1_funct_1(E_145))), inference(resolution, [status(thm)], [c_62, c_1509])).
% 5.49/2.01  tff(c_2153, plain, (![A_179, B_180, E_181]: (k1_partfun1(A_179, B_180, '#skF_2', '#skF_1', E_181, '#skF_4')=k5_relat_1(E_181, '#skF_4') | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~v1_funct_1(E_181))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1525])).
% 5.49/2.01  tff(c_2189, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2153])).
% 5.49/2.01  tff(c_2206, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2189])).
% 5.49/2.01  tff(c_40, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.49/2.01  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.49/2.01  tff(c_273, plain, (![D_79, C_80, A_81, B_82]: (D_79=C_80 | ~r2_relset_1(A_81, B_82, C_80, D_79) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.49/2.01  tff(c_281, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_273])).
% 5.49/2.01  tff(c_296, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_281])).
% 5.49/2.01  tff(c_423, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_296])).
% 5.49/2.01  tff(c_2210, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2206, c_423])).
% 5.49/2.01  tff(c_2214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1335, c_2210])).
% 5.49/2.01  tff(c_2215, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_296])).
% 5.49/2.01  tff(c_3164, plain, (![E_216, A_213, D_214, B_217, C_218, F_215]: (k1_partfun1(A_213, B_217, C_218, D_214, E_216, F_215)=k5_relat_1(E_216, F_215) | ~m1_subset_1(F_215, k1_zfmisc_1(k2_zfmisc_1(C_218, D_214))) | ~v1_funct_1(F_215) | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_213, B_217))) | ~v1_funct_1(E_216))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.49/2.01  tff(c_3180, plain, (![A_213, B_217, E_216]: (k1_partfun1(A_213, B_217, '#skF_2', '#skF_1', E_216, '#skF_4')=k5_relat_1(E_216, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_213, B_217))) | ~v1_funct_1(E_216))), inference(resolution, [status(thm)], [c_62, c_3164])).
% 5.49/2.01  tff(c_3808, plain, (![A_250, B_251, E_252]: (k1_partfun1(A_250, B_251, '#skF_2', '#skF_1', E_252, '#skF_4')=k5_relat_1(E_252, '#skF_4') | ~m1_subset_1(E_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))) | ~v1_funct_1(E_252))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3180])).
% 5.49/2.01  tff(c_3844, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_3808])).
% 5.49/2.01  tff(c_3861, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2215, c_3844])).
% 5.49/2.01  tff(c_3863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2864, c_3861])).
% 5.49/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/2.01  
% 5.49/2.01  Inference rules
% 5.49/2.01  ----------------------
% 5.49/2.01  #Ref     : 0
% 5.49/2.01  #Sup     : 877
% 5.49/2.01  #Fact    : 0
% 5.49/2.01  #Define  : 0
% 5.49/2.01  #Split   : 26
% 5.49/2.01  #Chain   : 0
% 5.49/2.01  #Close   : 0
% 5.49/2.01  
% 5.49/2.01  Ordering : KBO
% 5.49/2.01  
% 5.49/2.01  Simplification rules
% 5.49/2.01  ----------------------
% 5.49/2.01  #Subsume      : 15
% 5.49/2.01  #Demod        : 358
% 5.49/2.01  #Tautology    : 160
% 5.49/2.01  #SimpNegUnit  : 124
% 5.49/2.01  #BackRed      : 7
% 5.49/2.01  
% 5.49/2.01  #Partial instantiations: 0
% 5.49/2.01  #Strategies tried      : 1
% 5.49/2.01  
% 5.49/2.01  Timing (in seconds)
% 5.49/2.01  ----------------------
% 5.49/2.01  Preprocessing        : 0.35
% 5.49/2.01  Parsing              : 0.19
% 5.49/2.01  CNF conversion       : 0.02
% 5.49/2.01  Main loop            : 0.91
% 5.49/2.01  Inferencing          : 0.31
% 5.49/2.01  Reduction            : 0.32
% 5.49/2.01  Demodulation         : 0.24
% 5.49/2.01  BG Simplification    : 0.05
% 5.49/2.01  Subsumption          : 0.15
% 5.49/2.01  Abstraction          : 0.06
% 5.49/2.01  MUC search           : 0.00
% 5.49/2.01  Cooper               : 0.00
% 5.49/2.01  Total                : 1.31
% 5.49/2.01  Index Insertion      : 0.00
% 5.49/2.01  Index Deletion       : 0.00
% 5.49/2.01  Index Matching       : 0.00
% 5.49/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
