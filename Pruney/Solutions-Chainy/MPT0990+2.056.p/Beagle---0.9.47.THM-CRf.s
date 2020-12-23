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
% DateTime   : Thu Dec  3 10:13:03 EST 2020

% Result     : Theorem 13.38s
% Output     : CNFRefutation 13.49s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 567 expanded)
%              Number of leaves         :   38 ( 231 expanded)
%              Depth                    :   12
%              Number of atoms          :  380 (2897 expanded)
%              Number of equality atoms :  138 ( 934 expanded)
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

tff(f_172,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_114,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_146,axiom,(
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

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_112,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_130,axiom,(
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

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_126,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_133,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_126])).

tff(c_177,plain,(
    ! [B_63,A_64,C_65] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_64,B_63,C_65) = A_64
      | ~ v1_funct_2(C_65,A_64,B_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_180,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_177])).

tff(c_186,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_133,c_180])).

tff(c_187,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_186])).

tff(c_109,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_116,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_109])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_117,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_109])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_134,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_126])).

tff(c_183,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_177])).

tff(c_190,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_134,c_183])).

tff(c_191,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_190])).

tff(c_38,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10,plain,(
    ! [A_3,B_5] :
      ( k2_funct_1(A_3) = B_5
      | k6_relat_1(k1_relat_1(A_3)) != k5_relat_1(A_3,B_5)
      | k2_relat_1(A_3) != k1_relat_1(B_5)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8817,plain,(
    ! [A_441,B_442] :
      ( k2_funct_1(A_441) = B_442
      | k6_partfun1(k1_relat_1(A_441)) != k5_relat_1(A_441,B_442)
      | k2_relat_1(A_441) != k1_relat_1(B_442)
      | ~ v2_funct_1(A_441)
      | ~ v1_funct_1(B_442)
      | ~ v1_relat_1(B_442)
      | ~ v1_funct_1(A_441)
      | ~ v1_relat_1(A_441) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_8819,plain,(
    ! [B_442] :
      ( k2_funct_1('#skF_3') = B_442
      | k5_relat_1('#skF_3',B_442) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_442)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_442)
      | ~ v1_relat_1(B_442)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_8817])).

tff(c_17517,plain,(
    ! [B_749] :
      ( k2_funct_1('#skF_3') = B_749
      | k5_relat_1('#skF_3',B_749) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_749)
      | ~ v1_funct_1(B_749)
      | ~ v1_relat_1(B_749) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_72,c_56,c_8819])).

tff(c_17526,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_116,c_17517])).

tff(c_17535,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_187,c_17526])).

tff(c_17536,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_17535])).

tff(c_17537,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_17536])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_1] : k1_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_17788,plain,(
    ! [B_774,C_775,A_776] :
      ( k6_partfun1(B_774) = k5_relat_1(k2_funct_1(C_775),C_775)
      | k1_xboole_0 = B_774
      | ~ v2_funct_1(C_775)
      | k2_relset_1(A_776,B_774,C_775) != B_774
      | ~ m1_subset_1(C_775,k1_zfmisc_1(k2_zfmisc_1(A_776,B_774)))
      | ~ v1_funct_2(C_775,A_776,B_774)
      | ~ v1_funct_1(C_775) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_17796,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_17788])).

tff(c_17808,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_17796])).

tff(c_17809,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_17808])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_partfun1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6])).

tff(c_17813,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17809,c_75])).

tff(c_17820,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_72,c_56,c_17813])).

tff(c_17827,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17820,c_77])).

tff(c_17833,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_17827])).

tff(c_17835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17537,c_17833])).

tff(c_17836,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_17536])).

tff(c_555,plain,(
    ! [E_127,B_126,D_122,A_123,C_124,F_125] :
      ( k1_partfun1(A_123,B_126,C_124,D_122,E_127,F_125) = k5_relat_1(E_127,F_125)
      | ~ m1_subset_1(F_125,k1_zfmisc_1(k2_zfmisc_1(C_124,D_122)))
      | ~ v1_funct_1(F_125)
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_123,B_126)))
      | ~ v1_funct_1(E_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_557,plain,(
    ! [A_123,B_126,E_127] :
      ( k1_partfun1(A_123,B_126,'#skF_2','#skF_1',E_127,'#skF_4') = k5_relat_1(E_127,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_123,B_126)))
      | ~ v1_funct_1(E_127) ) ),
    inference(resolution,[status(thm)],[c_62,c_555])).

tff(c_566,plain,(
    ! [A_128,B_129,E_130] :
      ( k1_partfun1(A_128,B_129,'#skF_2','#skF_1',E_130,'#skF_4') = k5_relat_1(E_130,'#skF_4')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_557])).

tff(c_572,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_566])).

tff(c_578,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_572])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_206,plain,(
    ! [D_66,C_67,A_68,B_69] :
      ( D_66 = C_67
      | ~ r2_relset_1(A_68,B_69,C_67,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_217,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_206])).

tff(c_239,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_646,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_239])).

tff(c_803,plain,(
    ! [C_154,E_155,F_158,B_156,D_159,A_157] :
      ( m1_subset_1(k1_partfun1(A_157,B_156,C_154,D_159,E_155,F_158),k1_zfmisc_1(k2_zfmisc_1(A_157,D_159)))
      | ~ m1_subset_1(F_158,k1_zfmisc_1(k2_zfmisc_1(C_154,D_159)))
      | ~ v1_funct_1(F_158)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156)))
      | ~ v1_funct_1(E_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_870,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_803])).

tff(c_899,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_870])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_899])).

tff(c_902,plain,
    ( ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_8841,plain,(
    ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_902])).

tff(c_226,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_funct_1(k2_funct_1(C_70))
      | k2_relset_1(A_71,B_72,C_70) != B_72
      | ~ v2_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_70,A_71,B_72)
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_232,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_226])).

tff(c_238,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_60,c_232])).

tff(c_40,plain,(
    ! [C_34,B_33,A_32] :
      ( m1_subset_1(k2_funct_1(C_34),k1_zfmisc_1(k2_zfmisc_1(B_33,A_32)))
      | k2_relset_1(A_32,B_33,C_34) != B_33
      | ~ v2_funct_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ v1_funct_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_9375,plain,(
    ! [F_505,D_502,C_504,A_503,B_506,E_507] :
      ( k1_partfun1(A_503,B_506,C_504,D_502,E_507,F_505) = k5_relat_1(E_507,F_505)
      | ~ m1_subset_1(F_505,k1_zfmisc_1(k2_zfmisc_1(C_504,D_502)))
      | ~ v1_funct_1(F_505)
      | ~ m1_subset_1(E_507,k1_zfmisc_1(k2_zfmisc_1(A_503,B_506)))
      | ~ v1_funct_1(E_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_9381,plain,(
    ! [A_503,B_506,E_507] :
      ( k1_partfun1(A_503,B_506,'#skF_2','#skF_1',E_507,'#skF_4') = k5_relat_1(E_507,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_507,k1_zfmisc_1(k2_zfmisc_1(A_503,B_506)))
      | ~ v1_funct_1(E_507) ) ),
    inference(resolution,[status(thm)],[c_62,c_9375])).

tff(c_9394,plain,(
    ! [A_508,B_509,E_510] :
      ( k1_partfun1(A_508,B_509,'#skF_2','#skF_1',E_510,'#skF_4') = k5_relat_1(E_510,'#skF_4')
      | ~ m1_subset_1(E_510,k1_zfmisc_1(k2_zfmisc_1(A_508,B_509)))
      | ~ v1_funct_1(E_510) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9381])).

tff(c_16509,plain,(
    ! [B_725,A_726,C_727] :
      ( k1_partfun1(B_725,A_726,'#skF_2','#skF_1',k2_funct_1(C_727),'#skF_4') = k5_relat_1(k2_funct_1(C_727),'#skF_4')
      | ~ v1_funct_1(k2_funct_1(C_727))
      | k2_relset_1(A_726,B_725,C_727) != B_725
      | ~ v2_funct_1(C_727)
      | ~ m1_subset_1(C_727,k1_zfmisc_1(k2_zfmisc_1(A_726,B_725)))
      | ~ v1_funct_2(C_727,A_726,B_725)
      | ~ v1_funct_1(C_727) ) ),
    inference(resolution,[status(thm)],[c_40,c_9394])).

tff(c_16566,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_2','#skF_1',k2_funct_1('#skF_3'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_16509])).

tff(c_16619,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_2','#skF_1',k2_funct_1('#skF_3'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_60,c_238,c_16566])).

tff(c_9629,plain,(
    ! [D_522,C_517,F_521,B_519,A_520,E_518] :
      ( m1_subset_1(k1_partfun1(A_520,B_519,C_517,D_522,E_518,F_521),k1_zfmisc_1(k2_zfmisc_1(A_520,D_522)))
      | ~ m1_subset_1(F_521,k1_zfmisc_1(k2_zfmisc_1(C_517,D_522)))
      | ~ v1_funct_1(F_521)
      | ~ m1_subset_1(E_518,k1_zfmisc_1(k2_zfmisc_1(A_520,B_519)))
      | ~ v1_funct_1(E_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    ! [B_17,A_16,C_18] :
      ( k1_xboole_0 = B_17
      | k1_relset_1(A_16,B_17,C_18) = A_16
      | ~ v1_funct_2(C_18,A_16,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_9698,plain,(
    ! [D_522,C_517,F_521,B_519,A_520,E_518] :
      ( k1_xboole_0 = D_522
      | k1_relset_1(A_520,D_522,k1_partfun1(A_520,B_519,C_517,D_522,E_518,F_521)) = A_520
      | ~ v1_funct_2(k1_partfun1(A_520,B_519,C_517,D_522,E_518,F_521),A_520,D_522)
      | ~ m1_subset_1(F_521,k1_zfmisc_1(k2_zfmisc_1(C_517,D_522)))
      | ~ v1_funct_1(F_521)
      | ~ m1_subset_1(E_518,k1_zfmisc_1(k2_zfmisc_1(A_520,B_519)))
      | ~ v1_funct_1(E_518) ) ),
    inference(resolution,[status(thm)],[c_9629,c_30])).

tff(c_16642,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k1_partfun1('#skF_2','#skF_1','#skF_2','#skF_1',k2_funct_1('#skF_3'),'#skF_4')) = '#skF_2'
    | ~ v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'),'#skF_4'),'#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16619,c_9698])).

tff(c_16673,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k5_relat_1(k2_funct_1('#skF_3'),'#skF_4')) = '#skF_2'
    | ~ v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'),'#skF_4'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_66,c_62,c_16619,c_16642])).

tff(c_16674,plain,
    ( k1_relset_1('#skF_2','#skF_1',k5_relat_1(k2_funct_1('#skF_3'),'#skF_4')) = '#skF_2'
    | ~ v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'),'#skF_4'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_16673])).

tff(c_16889,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_16674])).

tff(c_16892,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_16889])).

tff(c_16896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_56,c_60,c_16892])).

tff(c_16898,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_16674])).

tff(c_9491,plain,(
    ! [A_514,C_515,B_516] :
      ( k6_partfun1(A_514) = k5_relat_1(C_515,k2_funct_1(C_515))
      | k1_xboole_0 = B_516
      | ~ v2_funct_1(C_515)
      | k2_relset_1(A_514,B_516,C_515) != B_516
      | ~ m1_subset_1(C_515,k1_zfmisc_1(k2_zfmisc_1(A_514,B_516)))
      | ~ v1_funct_2(C_515,A_514,B_516)
      | ~ v1_funct_1(C_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_9497,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_9491])).

tff(c_9505,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_9497])).

tff(c_9506,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_9505])).

tff(c_12241,plain,(
    ! [C_604,A_605,A_606,E_602,B_607,B_603] :
      ( k1_partfun1(A_606,B_607,B_603,A_605,E_602,k2_funct_1(C_604)) = k5_relat_1(E_602,k2_funct_1(C_604))
      | ~ v1_funct_1(k2_funct_1(C_604))
      | ~ m1_subset_1(E_602,k1_zfmisc_1(k2_zfmisc_1(A_606,B_607)))
      | ~ v1_funct_1(E_602)
      | k2_relset_1(A_605,B_603,C_604) != B_603
      | ~ v2_funct_1(C_604)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(A_605,B_603)))
      | ~ v1_funct_2(C_604,A_605,B_603)
      | ~ v1_funct_1(C_604) ) ),
    inference(resolution,[status(thm)],[c_40,c_9375])).

tff(c_12273,plain,(
    ! [B_603,A_605,C_604] :
      ( k1_partfun1('#skF_1','#skF_2',B_603,A_605,'#skF_3',k2_funct_1(C_604)) = k5_relat_1('#skF_3',k2_funct_1(C_604))
      | ~ v1_funct_1(k2_funct_1(C_604))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_605,B_603,C_604) != B_603
      | ~ v2_funct_1(C_604)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(A_605,B_603)))
      | ~ v1_funct_2(C_604,A_605,B_603)
      | ~ v1_funct_1(C_604) ) ),
    inference(resolution,[status(thm)],[c_68,c_12241])).

tff(c_17197,plain,(
    ! [B_731,A_732,C_733] :
      ( k1_partfun1('#skF_1','#skF_2',B_731,A_732,'#skF_3',k2_funct_1(C_733)) = k5_relat_1('#skF_3',k2_funct_1(C_733))
      | ~ v1_funct_1(k2_funct_1(C_733))
      | k2_relset_1(A_732,B_731,C_733) != B_731
      | ~ v2_funct_1(C_733)
      | ~ m1_subset_1(C_733,k1_zfmisc_1(k2_zfmisc_1(A_732,B_731)))
      | ~ v1_funct_2(C_733,A_732,B_731)
      | ~ v1_funct_1(C_733) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_12273])).

tff(c_17257,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_17197])).

tff(c_17313,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_60,c_238,c_9506,c_17257])).

tff(c_32,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] :
      ( m1_subset_1(k1_partfun1(A_19,B_20,C_21,D_22,E_23,F_24),k1_zfmisc_1(k2_zfmisc_1(A_19,D_22)))
      | ~ m1_subset_1(F_24,k1_zfmisc_1(k2_zfmisc_1(C_21,D_22)))
      | ~ v1_funct_1(F_24)
      | ~ m1_subset_1(E_23,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_1(E_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_17345,plain,
    ( m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17313,c_32])).

tff(c_17374,plain,(
    m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_238,c_16898,c_17345])).

tff(c_17376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8841,c_17374])).

tff(c_17377,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_902])).

tff(c_17952,plain,(
    ! [E_789,C_786,B_788,A_785,F_787,D_784] :
      ( k1_partfun1(A_785,B_788,C_786,D_784,E_789,F_787) = k5_relat_1(E_789,F_787)
      | ~ m1_subset_1(F_787,k1_zfmisc_1(k2_zfmisc_1(C_786,D_784)))
      | ~ v1_funct_1(F_787)
      | ~ m1_subset_1(E_789,k1_zfmisc_1(k2_zfmisc_1(A_785,B_788)))
      | ~ v1_funct_1(E_789) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_17958,plain,(
    ! [A_785,B_788,E_789] :
      ( k1_partfun1(A_785,B_788,'#skF_2','#skF_1',E_789,'#skF_4') = k5_relat_1(E_789,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_789,k1_zfmisc_1(k2_zfmisc_1(A_785,B_788)))
      | ~ v1_funct_1(E_789) ) ),
    inference(resolution,[status(thm)],[c_62,c_17952])).

tff(c_17971,plain,(
    ! [A_790,B_791,E_792] :
      ( k1_partfun1(A_790,B_791,'#skF_2','#skF_1',E_792,'#skF_4') = k5_relat_1(E_792,'#skF_4')
      | ~ m1_subset_1(E_792,k1_zfmisc_1(k2_zfmisc_1(A_790,B_791)))
      | ~ v1_funct_1(E_792) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_17958])).

tff(c_17983,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_17971])).

tff(c_17993,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_17377,c_17983])).

tff(c_17995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17836,c_17993])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:31:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.38/6.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.38/6.04  
% 13.38/6.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.38/6.04  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.38/6.04  
% 13.38/6.04  %Foreground sorts:
% 13.38/6.04  
% 13.38/6.04  
% 13.38/6.04  %Background operators:
% 13.38/6.04  
% 13.38/6.04  
% 13.38/6.04  %Foreground operators:
% 13.38/6.04  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.38/6.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.38/6.04  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.38/6.04  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.38/6.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.38/6.04  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 13.38/6.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.38/6.04  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.38/6.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.38/6.04  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.38/6.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.38/6.04  tff('#skF_2', type, '#skF_2': $i).
% 13.38/6.04  tff('#skF_3', type, '#skF_3': $i).
% 13.38/6.04  tff('#skF_1', type, '#skF_1': $i).
% 13.38/6.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.38/6.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.38/6.04  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.38/6.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.38/6.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.38/6.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.38/6.04  tff('#skF_4', type, '#skF_4': $i).
% 13.38/6.04  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.38/6.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.38/6.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.38/6.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.38/6.04  
% 13.49/6.06  tff(f_172, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 13.49/6.06  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.49/6.06  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.49/6.06  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.49/6.06  tff(f_114, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 13.49/6.06  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 13.49/6.06  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 13.49/6.06  tff(f_146, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 13.49/6.06  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 13.49/6.06  tff(f_112, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 13.49/6.06  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 13.49/6.06  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 13.49/6.06  tff(f_130, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 13.49/6.06  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_126, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.49/6.06  tff(c_133, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_126])).
% 13.49/6.06  tff(c_177, plain, (![B_63, A_64, C_65]: (k1_xboole_0=B_63 | k1_relset_1(A_64, B_63, C_65)=A_64 | ~v1_funct_2(C_65, A_64, B_63) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.49/6.06  tff(c_180, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_177])).
% 13.49/6.06  tff(c_186, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_133, c_180])).
% 13.49/6.06  tff(c_187, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_186])).
% 13.49/6.06  tff(c_109, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.49/6.06  tff(c_116, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_109])).
% 13.49/6.06  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_117, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_109])).
% 13.49/6.06  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_134, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_126])).
% 13.49/6.06  tff(c_183, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_177])).
% 13.49/6.06  tff(c_190, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_134, c_183])).
% 13.49/6.06  tff(c_191, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_190])).
% 13.49/6.06  tff(c_38, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.49/6.06  tff(c_10, plain, (![A_3, B_5]: (k2_funct_1(A_3)=B_5 | k6_relat_1(k1_relat_1(A_3))!=k5_relat_1(A_3, B_5) | k2_relat_1(A_3)!=k1_relat_1(B_5) | ~v2_funct_1(A_3) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.49/6.06  tff(c_8817, plain, (![A_441, B_442]: (k2_funct_1(A_441)=B_442 | k6_partfun1(k1_relat_1(A_441))!=k5_relat_1(A_441, B_442) | k2_relat_1(A_441)!=k1_relat_1(B_442) | ~v2_funct_1(A_441) | ~v1_funct_1(B_442) | ~v1_relat_1(B_442) | ~v1_funct_1(A_441) | ~v1_relat_1(A_441))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_10])).
% 13.49/6.06  tff(c_8819, plain, (![B_442]: (k2_funct_1('#skF_3')=B_442 | k5_relat_1('#skF_3', B_442)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_442) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_442) | ~v1_relat_1(B_442) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_8817])).
% 13.49/6.06  tff(c_17517, plain, (![B_749]: (k2_funct_1('#skF_3')=B_749 | k5_relat_1('#skF_3', B_749)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_749) | ~v1_funct_1(B_749) | ~v1_relat_1(B_749))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_72, c_56, c_8819])).
% 13.49/6.06  tff(c_17526, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_116, c_17517])).
% 13.49/6.06  tff(c_17535, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_187, c_17526])).
% 13.49/6.06  tff(c_17536, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_17535])).
% 13.49/6.06  tff(c_17537, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_17536])).
% 13.49/6.06  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.49/6.06  tff(c_77, plain, (![A_1]: (k1_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2])).
% 13.49/6.06  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_17788, plain, (![B_774, C_775, A_776]: (k6_partfun1(B_774)=k5_relat_1(k2_funct_1(C_775), C_775) | k1_xboole_0=B_774 | ~v2_funct_1(C_775) | k2_relset_1(A_776, B_774, C_775)!=B_774 | ~m1_subset_1(C_775, k1_zfmisc_1(k2_zfmisc_1(A_776, B_774))) | ~v1_funct_2(C_775, A_776, B_774) | ~v1_funct_1(C_775))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.49/6.06  tff(c_17796, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_17788])).
% 13.49/6.06  tff(c_17808, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_17796])).
% 13.49/6.06  tff(c_17809, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_17808])).
% 13.49/6.06  tff(c_6, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.49/6.06  tff(c_75, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_partfun1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6])).
% 13.49/6.06  tff(c_17813, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17809, c_75])).
% 13.49/6.06  tff(c_17820, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_72, c_56, c_17813])).
% 13.49/6.06  tff(c_17827, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17820, c_77])).
% 13.49/6.06  tff(c_17833, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_17827])).
% 13.49/6.06  tff(c_17835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17537, c_17833])).
% 13.49/6.06  tff(c_17836, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_17536])).
% 13.49/6.06  tff(c_555, plain, (![E_127, B_126, D_122, A_123, C_124, F_125]: (k1_partfun1(A_123, B_126, C_124, D_122, E_127, F_125)=k5_relat_1(E_127, F_125) | ~m1_subset_1(F_125, k1_zfmisc_1(k2_zfmisc_1(C_124, D_122))) | ~v1_funct_1(F_125) | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_123, B_126))) | ~v1_funct_1(E_127))), inference(cnfTransformation, [status(thm)], [f_112])).
% 13.49/6.06  tff(c_557, plain, (![A_123, B_126, E_127]: (k1_partfun1(A_123, B_126, '#skF_2', '#skF_1', E_127, '#skF_4')=k5_relat_1(E_127, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_123, B_126))) | ~v1_funct_1(E_127))), inference(resolution, [status(thm)], [c_62, c_555])).
% 13.49/6.06  tff(c_566, plain, (![A_128, B_129, E_130]: (k1_partfun1(A_128, B_129, '#skF_2', '#skF_1', E_130, '#skF_4')=k5_relat_1(E_130, '#skF_4') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_1(E_130))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_557])).
% 13.49/6.06  tff(c_572, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_566])).
% 13.49/6.06  tff(c_578, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_572])).
% 13.49/6.06  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.49/6.06  tff(c_206, plain, (![D_66, C_67, A_68, B_69]: (D_66=C_67 | ~r2_relset_1(A_68, B_69, C_67, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.49/6.06  tff(c_217, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_206])).
% 13.49/6.06  tff(c_239, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_217])).
% 13.49/6.06  tff(c_646, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_239])).
% 13.49/6.06  tff(c_803, plain, (![C_154, E_155, F_158, B_156, D_159, A_157]: (m1_subset_1(k1_partfun1(A_157, B_156, C_154, D_159, E_155, F_158), k1_zfmisc_1(k2_zfmisc_1(A_157, D_159))) | ~m1_subset_1(F_158, k1_zfmisc_1(k2_zfmisc_1(C_154, D_159))) | ~v1_funct_1(F_158) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))) | ~v1_funct_1(E_155))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.49/6.06  tff(c_870, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_578, c_803])).
% 13.49/6.06  tff(c_899, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_870])).
% 13.49/6.06  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_899])).
% 13.49/6.06  tff(c_902, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_217])).
% 13.49/6.06  tff(c_8841, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_902])).
% 13.49/6.06  tff(c_226, plain, (![C_70, A_71, B_72]: (v1_funct_1(k2_funct_1(C_70)) | k2_relset_1(A_71, B_72, C_70)!=B_72 | ~v2_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_funct_2(C_70, A_71, B_72) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.49/6.06  tff(c_232, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_226])).
% 13.49/6.06  tff(c_238, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_60, c_232])).
% 13.49/6.06  tff(c_40, plain, (![C_34, B_33, A_32]: (m1_subset_1(k2_funct_1(C_34), k1_zfmisc_1(k2_zfmisc_1(B_33, A_32))) | k2_relset_1(A_32, B_33, C_34)!=B_33 | ~v2_funct_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(C_34, A_32, B_33) | ~v1_funct_1(C_34))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.49/6.06  tff(c_9375, plain, (![F_505, D_502, C_504, A_503, B_506, E_507]: (k1_partfun1(A_503, B_506, C_504, D_502, E_507, F_505)=k5_relat_1(E_507, F_505) | ~m1_subset_1(F_505, k1_zfmisc_1(k2_zfmisc_1(C_504, D_502))) | ~v1_funct_1(F_505) | ~m1_subset_1(E_507, k1_zfmisc_1(k2_zfmisc_1(A_503, B_506))) | ~v1_funct_1(E_507))), inference(cnfTransformation, [status(thm)], [f_112])).
% 13.49/6.06  tff(c_9381, plain, (![A_503, B_506, E_507]: (k1_partfun1(A_503, B_506, '#skF_2', '#skF_1', E_507, '#skF_4')=k5_relat_1(E_507, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_507, k1_zfmisc_1(k2_zfmisc_1(A_503, B_506))) | ~v1_funct_1(E_507))), inference(resolution, [status(thm)], [c_62, c_9375])).
% 13.49/6.06  tff(c_9394, plain, (![A_508, B_509, E_510]: (k1_partfun1(A_508, B_509, '#skF_2', '#skF_1', E_510, '#skF_4')=k5_relat_1(E_510, '#skF_4') | ~m1_subset_1(E_510, k1_zfmisc_1(k2_zfmisc_1(A_508, B_509))) | ~v1_funct_1(E_510))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9381])).
% 13.49/6.06  tff(c_16509, plain, (![B_725, A_726, C_727]: (k1_partfun1(B_725, A_726, '#skF_2', '#skF_1', k2_funct_1(C_727), '#skF_4')=k5_relat_1(k2_funct_1(C_727), '#skF_4') | ~v1_funct_1(k2_funct_1(C_727)) | k2_relset_1(A_726, B_725, C_727)!=B_725 | ~v2_funct_1(C_727) | ~m1_subset_1(C_727, k1_zfmisc_1(k2_zfmisc_1(A_726, B_725))) | ~v1_funct_2(C_727, A_726, B_725) | ~v1_funct_1(C_727))), inference(resolution, [status(thm)], [c_40, c_9394])).
% 13.49/6.06  tff(c_16566, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_2', '#skF_1', k2_funct_1('#skF_3'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_16509])).
% 13.49/6.06  tff(c_16619, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_2', '#skF_1', k2_funct_1('#skF_3'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_60, c_238, c_16566])).
% 13.49/6.06  tff(c_9629, plain, (![D_522, C_517, F_521, B_519, A_520, E_518]: (m1_subset_1(k1_partfun1(A_520, B_519, C_517, D_522, E_518, F_521), k1_zfmisc_1(k2_zfmisc_1(A_520, D_522))) | ~m1_subset_1(F_521, k1_zfmisc_1(k2_zfmisc_1(C_517, D_522))) | ~v1_funct_1(F_521) | ~m1_subset_1(E_518, k1_zfmisc_1(k2_zfmisc_1(A_520, B_519))) | ~v1_funct_1(E_518))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.49/6.06  tff(c_30, plain, (![B_17, A_16, C_18]: (k1_xboole_0=B_17 | k1_relset_1(A_16, B_17, C_18)=A_16 | ~v1_funct_2(C_18, A_16, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.49/6.06  tff(c_9698, plain, (![D_522, C_517, F_521, B_519, A_520, E_518]: (k1_xboole_0=D_522 | k1_relset_1(A_520, D_522, k1_partfun1(A_520, B_519, C_517, D_522, E_518, F_521))=A_520 | ~v1_funct_2(k1_partfun1(A_520, B_519, C_517, D_522, E_518, F_521), A_520, D_522) | ~m1_subset_1(F_521, k1_zfmisc_1(k2_zfmisc_1(C_517, D_522))) | ~v1_funct_1(F_521) | ~m1_subset_1(E_518, k1_zfmisc_1(k2_zfmisc_1(A_520, B_519))) | ~v1_funct_1(E_518))), inference(resolution, [status(thm)], [c_9629, c_30])).
% 13.49/6.06  tff(c_16642, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k1_partfun1('#skF_2', '#skF_1', '#skF_2', '#skF_1', k2_funct_1('#skF_3'), '#skF_4'))='#skF_2' | ~v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'), '#skF_4'), '#skF_2', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16619, c_9698])).
% 13.49/6.06  tff(c_16673, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k5_relat_1(k2_funct_1('#skF_3'), '#skF_4'))='#skF_2' | ~v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'), '#skF_4'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_66, c_62, c_16619, c_16642])).
% 13.49/6.06  tff(c_16674, plain, (k1_relset_1('#skF_2', '#skF_1', k5_relat_1(k2_funct_1('#skF_3'), '#skF_4'))='#skF_2' | ~v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'), '#skF_4'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_16673])).
% 13.49/6.06  tff(c_16889, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_16674])).
% 13.49/6.06  tff(c_16892, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_16889])).
% 13.49/6.06  tff(c_16896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_56, c_60, c_16892])).
% 13.49/6.06  tff(c_16898, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_16674])).
% 13.49/6.06  tff(c_9491, plain, (![A_514, C_515, B_516]: (k6_partfun1(A_514)=k5_relat_1(C_515, k2_funct_1(C_515)) | k1_xboole_0=B_516 | ~v2_funct_1(C_515) | k2_relset_1(A_514, B_516, C_515)!=B_516 | ~m1_subset_1(C_515, k1_zfmisc_1(k2_zfmisc_1(A_514, B_516))) | ~v1_funct_2(C_515, A_514, B_516) | ~v1_funct_1(C_515))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.49/6.06  tff(c_9497, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_9491])).
% 13.49/6.06  tff(c_9505, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_9497])).
% 13.49/6.06  tff(c_9506, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_9505])).
% 13.49/6.06  tff(c_12241, plain, (![C_604, A_605, A_606, E_602, B_607, B_603]: (k1_partfun1(A_606, B_607, B_603, A_605, E_602, k2_funct_1(C_604))=k5_relat_1(E_602, k2_funct_1(C_604)) | ~v1_funct_1(k2_funct_1(C_604)) | ~m1_subset_1(E_602, k1_zfmisc_1(k2_zfmisc_1(A_606, B_607))) | ~v1_funct_1(E_602) | k2_relset_1(A_605, B_603, C_604)!=B_603 | ~v2_funct_1(C_604) | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(A_605, B_603))) | ~v1_funct_2(C_604, A_605, B_603) | ~v1_funct_1(C_604))), inference(resolution, [status(thm)], [c_40, c_9375])).
% 13.49/6.06  tff(c_12273, plain, (![B_603, A_605, C_604]: (k1_partfun1('#skF_1', '#skF_2', B_603, A_605, '#skF_3', k2_funct_1(C_604))=k5_relat_1('#skF_3', k2_funct_1(C_604)) | ~v1_funct_1(k2_funct_1(C_604)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_605, B_603, C_604)!=B_603 | ~v2_funct_1(C_604) | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(A_605, B_603))) | ~v1_funct_2(C_604, A_605, B_603) | ~v1_funct_1(C_604))), inference(resolution, [status(thm)], [c_68, c_12241])).
% 13.49/6.06  tff(c_17197, plain, (![B_731, A_732, C_733]: (k1_partfun1('#skF_1', '#skF_2', B_731, A_732, '#skF_3', k2_funct_1(C_733))=k5_relat_1('#skF_3', k2_funct_1(C_733)) | ~v1_funct_1(k2_funct_1(C_733)) | k2_relset_1(A_732, B_731, C_733)!=B_731 | ~v2_funct_1(C_733) | ~m1_subset_1(C_733, k1_zfmisc_1(k2_zfmisc_1(A_732, B_731))) | ~v1_funct_2(C_733, A_732, B_731) | ~v1_funct_1(C_733))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_12273])).
% 13.49/6.06  tff(c_17257, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_17197])).
% 13.49/6.06  tff(c_17313, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_60, c_238, c_9506, c_17257])).
% 13.49/6.06  tff(c_32, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (m1_subset_1(k1_partfun1(A_19, B_20, C_21, D_22, E_23, F_24), k1_zfmisc_1(k2_zfmisc_1(A_19, D_22))) | ~m1_subset_1(F_24, k1_zfmisc_1(k2_zfmisc_1(C_21, D_22))) | ~v1_funct_1(F_24) | ~m1_subset_1(E_23, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_1(E_23))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.49/6.06  tff(c_17345, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17313, c_32])).
% 13.49/6.06  tff(c_17374, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_238, c_16898, c_17345])).
% 13.49/6.06  tff(c_17376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8841, c_17374])).
% 13.49/6.06  tff(c_17377, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_902])).
% 13.49/6.06  tff(c_17952, plain, (![E_789, C_786, B_788, A_785, F_787, D_784]: (k1_partfun1(A_785, B_788, C_786, D_784, E_789, F_787)=k5_relat_1(E_789, F_787) | ~m1_subset_1(F_787, k1_zfmisc_1(k2_zfmisc_1(C_786, D_784))) | ~v1_funct_1(F_787) | ~m1_subset_1(E_789, k1_zfmisc_1(k2_zfmisc_1(A_785, B_788))) | ~v1_funct_1(E_789))), inference(cnfTransformation, [status(thm)], [f_112])).
% 13.49/6.07  tff(c_17958, plain, (![A_785, B_788, E_789]: (k1_partfun1(A_785, B_788, '#skF_2', '#skF_1', E_789, '#skF_4')=k5_relat_1(E_789, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_789, k1_zfmisc_1(k2_zfmisc_1(A_785, B_788))) | ~v1_funct_1(E_789))), inference(resolution, [status(thm)], [c_62, c_17952])).
% 13.49/6.07  tff(c_17971, plain, (![A_790, B_791, E_792]: (k1_partfun1(A_790, B_791, '#skF_2', '#skF_1', E_792, '#skF_4')=k5_relat_1(E_792, '#skF_4') | ~m1_subset_1(E_792, k1_zfmisc_1(k2_zfmisc_1(A_790, B_791))) | ~v1_funct_1(E_792))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_17958])).
% 13.49/6.07  tff(c_17983, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_17971])).
% 13.49/6.07  tff(c_17993, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_17377, c_17983])).
% 13.49/6.07  tff(c_17995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17836, c_17993])).
% 13.49/6.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.49/6.07  
% 13.49/6.07  Inference rules
% 13.49/6.07  ----------------------
% 13.49/6.07  #Ref     : 0
% 13.49/6.07  #Sup     : 3414
% 13.49/6.07  #Fact    : 0
% 13.49/6.07  #Define  : 0
% 13.49/6.07  #Split   : 56
% 13.49/6.07  #Chain   : 0
% 13.49/6.07  #Close   : 0
% 13.49/6.07  
% 13.49/6.07  Ordering : KBO
% 13.49/6.07  
% 13.49/6.07  Simplification rules
% 13.49/6.07  ----------------------
% 13.49/6.07  #Subsume      : 636
% 13.49/6.07  #Demod        : 6446
% 13.49/6.07  #Tautology    : 504
% 13.49/6.07  #SimpNegUnit  : 552
% 13.49/6.07  #BackRed      : 133
% 13.49/6.07  
% 13.49/6.07  #Partial instantiations: 0
% 13.49/6.07  #Strategies tried      : 1
% 13.49/6.07  
% 13.49/6.07  Timing (in seconds)
% 13.49/6.07  ----------------------
% 13.49/6.07  Preprocessing        : 0.37
% 13.49/6.07  Parsing              : 0.20
% 13.49/6.07  CNF conversion       : 0.02
% 13.49/6.07  Main loop            : 4.88
% 13.49/6.07  Inferencing          : 1.10
% 13.49/6.07  Reduction            : 2.56
% 13.49/6.07  Demodulation         : 2.13
% 13.49/6.07  BG Simplification    : 0.09
% 13.49/6.07  Subsumption          : 0.92
% 13.49/6.07  Abstraction          : 0.16
% 13.49/6.07  MUC search           : 0.00
% 13.49/6.07  Cooper               : 0.00
% 13.49/6.07  Total                : 5.30
% 13.49/6.07  Index Insertion      : 0.00
% 13.49/6.07  Index Deletion       : 0.00
% 13.49/6.07  Index Matching       : 0.00
% 13.49/6.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
