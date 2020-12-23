%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:26 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 626 expanded)
%              Number of leaves         :   39 ( 239 expanded)
%              Depth                    :   17
%              Number of atoms          :  358 (2690 expanded)
%              Number of equality atoms :  137 ( 987 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_188,negated_conjecture,(
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

tff(f_103,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

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

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_120,axiom,(
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

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_146,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_69,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_32,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_114,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_114])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_630,plain,(
    ! [B_130,C_131,A_132] :
      ( k6_partfun1(B_130) = k5_relat_1(k2_funct_1(C_131),C_131)
      | k1_xboole_0 = B_130
      | ~ v2_funct_1(C_131)
      | k2_relset_1(A_132,B_130,C_131) != B_130
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_130)))
      | ~ v1_funct_2(C_131,A_132,B_130)
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_636,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_630])).

tff(c_646,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_636])).

tff(c_647,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_646])).

tff(c_720,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_24,plain,(
    ! [A_16] : m1_subset_1(k6_relat_1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_71,plain,(
    ! [A_16] : m1_subset_1(k6_partfun1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24])).

tff(c_133,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_relset_1(A_55,B_56,D_57,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_140,plain,(
    ! [A_16] : r2_relset_1(A_16,A_16,k6_partfun1(A_16),k6_partfun1(A_16)) ),
    inference(resolution,[status(thm)],[c_71,c_133])).

tff(c_472,plain,(
    ! [A_99,F_101,B_100,C_98,D_102,E_103] :
      ( m1_subset_1(k1_partfun1(A_99,B_100,C_98,D_102,E_103,F_101),k1_zfmisc_1(k2_zfmisc_1(A_99,D_102)))
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(C_98,D_102)))
      | ~ v1_funct_1(F_101)
      | ~ m1_subset_1(E_103,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_1(E_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_162,plain,(
    ! [D_61,C_62,A_63,B_64] :
      ( D_61 = C_62
      | ~ r2_relset_1(A_63,B_64,C_62,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_170,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_162])).

tff(c_185,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_170])).

tff(c_186,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_492,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_472,c_186])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_492])).

tff(c_515,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_1172,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k2_relset_1(A_158,B_159,C_160) = B_159
      | ~ r2_relset_1(B_159,B_159,k1_partfun1(B_159,A_158,A_158,B_159,D_161,C_160),k6_partfun1(B_159))
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_159,A_158)))
      | ~ v1_funct_2(D_161,B_159,A_158)
      | ~ v1_funct_1(D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_2(C_160,A_158,B_159)
      | ~ v1_funct_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1178,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_1172])).

tff(c_1182,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_140,c_1178])).

tff(c_1184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_720,c_1182])).

tff(c_1185,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_1193,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1185])).

tff(c_12,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_75,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1623,plain,(
    ! [D_184,E_185,A_182,B_186,C_183] :
      ( k1_xboole_0 = C_183
      | v2_funct_1(E_185)
      | k2_relset_1(A_182,B_186,D_184) != B_186
      | ~ v2_funct_1(k1_partfun1(A_182,B_186,B_186,C_183,D_184,E_185))
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(B_186,C_183)))
      | ~ v1_funct_2(E_185,B_186,C_183)
      | ~ v1_funct_1(E_185)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_186)))
      | ~ v1_funct_2(D_184,A_182,B_186)
      | ~ v1_funct_1(D_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1629,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_515,c_1623])).

tff(c_1637,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_75,c_58,c_1629])).

tff(c_1639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1193,c_52,c_1637])).

tff(c_1641,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1185])).

tff(c_1640,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1185])).

tff(c_14,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_relat_1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_partfun1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_1647,plain,
    ( k6_partfun1(k2_relat_1('#skF_4')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1640,c_74])).

tff(c_1657,plain,(
    k6_partfun1(k2_relat_1('#skF_4')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_64,c_1641,c_1647])).

tff(c_1683,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_78])).

tff(c_1703,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1683])).

tff(c_120,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_114])).

tff(c_129,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_120])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1741,plain,(
    ! [A_190,C_191,B_192] :
      ( k6_partfun1(A_190) = k5_relat_1(C_191,k2_funct_1(C_191))
      | k1_xboole_0 = B_192
      | ~ v2_funct_1(C_191)
      | k2_relset_1(A_190,B_192,C_191) != B_192
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_190,B_192)))
      | ~ v1_funct_2(C_191,A_190,B_192)
      | ~ v1_funct_1(C_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1745,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1741])).

tff(c_1753,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_1745])).

tff(c_1754,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1753])).

tff(c_16,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_73,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_partfun1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_1762,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1754,c_73])).

tff(c_1769,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_70,c_54,c_1762])).

tff(c_1793,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1769,c_78])).

tff(c_1811,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1793])).

tff(c_634,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_630])).

tff(c_642,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_634])).

tff(c_643,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_642])).

tff(c_653,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_74])).

tff(c_663,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_70,c_54,c_653])).

tff(c_18,plain,(
    ! [A_9,B_11] :
      ( k2_funct_1(A_9) = B_11
      | k6_relat_1(k2_relat_1(A_9)) != k5_relat_1(B_11,A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_72,plain,(
    ! [A_9,B_11] :
      ( k2_funct_1(A_9) = B_11
      | k6_partfun1(k2_relat_1(A_9)) != k5_relat_1(B_11,A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_18])).

tff(c_677,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_3') = B_11
      | k5_relat_1(B_11,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_11) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_72])).

tff(c_703,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_3') = B_11
      | k5_relat_1(B_11,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_11) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_70,c_54,c_677])).

tff(c_3889,plain,(
    ! [B_294] :
      ( k2_funct_1('#skF_3') = B_294
      | k5_relat_1(B_294,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_294) != '#skF_1'
      | ~ v1_funct_1(B_294)
      | ~ v1_relat_1(B_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1811,c_703])).

tff(c_3979,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_3889])).

tff(c_4074,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1703,c_3979])).

tff(c_4075,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4074])).

tff(c_689,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_78])).

tff(c_706,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_689])).

tff(c_584,plain,(
    ! [E_121,A_124,B_122,F_120,D_123,C_119] :
      ( k1_partfun1(A_124,B_122,C_119,D_123,E_121,F_120) = k5_relat_1(E_121,F_120)
      | ~ m1_subset_1(F_120,k1_zfmisc_1(k2_zfmisc_1(C_119,D_123)))
      | ~ v1_funct_1(F_120)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_1(E_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_590,plain,(
    ! [A_124,B_122,E_121] :
      ( k1_partfun1(A_124,B_122,'#skF_2','#skF_1',E_121,'#skF_4') = k5_relat_1(E_121,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_1(E_121) ) ),
    inference(resolution,[status(thm)],[c_60,c_584])).

tff(c_1708,plain,(
    ! [A_187,B_188,E_189] :
      ( k1_partfun1(A_187,B_188,'#skF_2','#skF_1',E_189,'#skF_4') = k5_relat_1(E_189,'#skF_4')
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(E_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_590])).

tff(c_1714,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1708])).

tff(c_1721,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_515,c_1714])).

tff(c_1186,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_1747,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1741])).

tff(c_1757,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1186,c_1641,c_1747])).

tff(c_1758,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1757])).

tff(c_1824,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1758,c_73])).

tff(c_1831,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_64,c_1641,c_1824])).

tff(c_1857,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1831,c_78])).

tff(c_1872,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1857])).

tff(c_1671,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k5_relat_1(B_11,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_72])).

tff(c_1700,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k5_relat_1(B_11,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_64,c_1641,c_1671])).

tff(c_5026,plain,(
    ! [B_340] :
      ( k2_funct_1('#skF_4') = B_340
      | k5_relat_1(B_340,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_340) != '#skF_2'
      | ~ v1_funct_1(B_340)
      | ~ v1_relat_1(B_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_1700])).

tff(c_5167,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_5026])).

tff(c_5290,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_706,c_1721,c_5167])).

tff(c_5295,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5290,c_1758])).

tff(c_5298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4075,c_5295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.80/2.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.87  
% 7.80/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.87  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.80/2.87  
% 7.80/2.87  %Foreground sorts:
% 7.80/2.87  
% 7.80/2.87  
% 7.80/2.87  %Background operators:
% 7.80/2.87  
% 7.80/2.87  
% 7.80/2.87  %Foreground operators:
% 7.80/2.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.80/2.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.80/2.87  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.80/2.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.80/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.80/2.87  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.80/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.80/2.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.80/2.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.80/2.87  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.80/2.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.80/2.87  tff('#skF_2', type, '#skF_2': $i).
% 7.80/2.87  tff('#skF_3', type, '#skF_3': $i).
% 7.80/2.87  tff('#skF_1', type, '#skF_1': $i).
% 7.80/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.80/2.87  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.80/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.80/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.80/2.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.80/2.87  tff('#skF_4', type, '#skF_4': $i).
% 7.80/2.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.80/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.80/2.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.80/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.80/2.87  
% 7.80/2.89  tff(f_188, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.80/2.89  tff(f_103, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.80/2.89  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.80/2.89  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.80/2.89  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.80/2.89  tff(f_162, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.80/2.89  tff(f_79, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.80/2.89  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.80/2.89  tff(f_91, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.80/2.89  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.80/2.89  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.80/2.89  tff(f_146, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.80/2.89  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.80/2.89  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 7.80/2.89  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.80/2.89  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_32, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.80/2.89  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.80/2.89  tff(c_78, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6])).
% 7.80/2.89  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.80/2.89  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_114, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.80/2.89  tff(c_123, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_114])).
% 7.80/2.89  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_123])).
% 7.80/2.89  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_630, plain, (![B_130, C_131, A_132]: (k6_partfun1(B_130)=k5_relat_1(k2_funct_1(C_131), C_131) | k1_xboole_0=B_130 | ~v2_funct_1(C_131) | k2_relset_1(A_132, B_130, C_131)!=B_130 | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_130))) | ~v1_funct_2(C_131, A_132, B_130) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.80/2.89  tff(c_636, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_630])).
% 7.80/2.89  tff(c_646, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_636])).
% 7.80/2.89  tff(c_647, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_646])).
% 7.80/2.89  tff(c_720, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_647])).
% 7.80/2.89  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_24, plain, (![A_16]: (m1_subset_1(k6_relat_1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.80/2.89  tff(c_71, plain, (![A_16]: (m1_subset_1(k6_partfun1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24])).
% 7.80/2.89  tff(c_133, plain, (![A_55, B_56, D_57]: (r2_relset_1(A_55, B_56, D_57, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.80/2.89  tff(c_140, plain, (![A_16]: (r2_relset_1(A_16, A_16, k6_partfun1(A_16), k6_partfun1(A_16)))), inference(resolution, [status(thm)], [c_71, c_133])).
% 7.80/2.89  tff(c_472, plain, (![A_99, F_101, B_100, C_98, D_102, E_103]: (m1_subset_1(k1_partfun1(A_99, B_100, C_98, D_102, E_103, F_101), k1_zfmisc_1(k2_zfmisc_1(A_99, D_102))) | ~m1_subset_1(F_101, k1_zfmisc_1(k2_zfmisc_1(C_98, D_102))) | ~v1_funct_1(F_101) | ~m1_subset_1(E_103, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_1(E_103))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.80/2.89  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_162, plain, (![D_61, C_62, A_63, B_64]: (D_61=C_62 | ~r2_relset_1(A_63, B_64, C_62, D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.80/2.89  tff(c_170, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_162])).
% 7.80/2.89  tff(c_185, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_170])).
% 7.80/2.89  tff(c_186, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_185])).
% 7.80/2.89  tff(c_492, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_472, c_186])).
% 7.80/2.89  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_492])).
% 7.80/2.89  tff(c_515, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_185])).
% 7.80/2.89  tff(c_1172, plain, (![A_158, B_159, C_160, D_161]: (k2_relset_1(A_158, B_159, C_160)=B_159 | ~r2_relset_1(B_159, B_159, k1_partfun1(B_159, A_158, A_158, B_159, D_161, C_160), k6_partfun1(B_159)) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_159, A_158))) | ~v1_funct_2(D_161, B_159, A_158) | ~v1_funct_1(D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_2(C_160, A_158, B_159) | ~v1_funct_1(C_160))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.80/2.89  tff(c_1178, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_515, c_1172])).
% 7.80/2.89  tff(c_1182, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_140, c_1178])).
% 7.80/2.89  tff(c_1184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_720, c_1182])).
% 7.80/2.89  tff(c_1185, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_647])).
% 7.80/2.89  tff(c_1193, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1185])).
% 7.80/2.89  tff(c_12, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.80/2.89  tff(c_75, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 7.80/2.89  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_1623, plain, (![D_184, E_185, A_182, B_186, C_183]: (k1_xboole_0=C_183 | v2_funct_1(E_185) | k2_relset_1(A_182, B_186, D_184)!=B_186 | ~v2_funct_1(k1_partfun1(A_182, B_186, B_186, C_183, D_184, E_185)) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(B_186, C_183))) | ~v1_funct_2(E_185, B_186, C_183) | ~v1_funct_1(E_185) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_186))) | ~v1_funct_2(D_184, A_182, B_186) | ~v1_funct_1(D_184))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.80/2.89  tff(c_1629, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_515, c_1623])).
% 7.80/2.89  tff(c_1637, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_75, c_58, c_1629])).
% 7.80/2.89  tff(c_1639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1193, c_52, c_1637])).
% 7.80/2.89  tff(c_1641, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1185])).
% 7.80/2.89  tff(c_1640, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1185])).
% 7.80/2.89  tff(c_14, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_relat_1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.80/2.89  tff(c_74, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_partfun1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14])).
% 7.80/2.89  tff(c_1647, plain, (k6_partfun1(k2_relat_1('#skF_4'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1640, c_74])).
% 7.80/2.89  tff(c_1657, plain, (k6_partfun1(k2_relat_1('#skF_4'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_64, c_1641, c_1647])).
% 7.80/2.89  tff(c_1683, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k2_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1657, c_78])).
% 7.80/2.89  tff(c_1703, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1683])).
% 7.80/2.89  tff(c_120, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_114])).
% 7.80/2.89  tff(c_129, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_120])).
% 7.80/2.89  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.80/2.89  tff(c_1741, plain, (![A_190, C_191, B_192]: (k6_partfun1(A_190)=k5_relat_1(C_191, k2_funct_1(C_191)) | k1_xboole_0=B_192 | ~v2_funct_1(C_191) | k2_relset_1(A_190, B_192, C_191)!=B_192 | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_190, B_192))) | ~v1_funct_2(C_191, A_190, B_192) | ~v1_funct_1(C_191))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.80/2.89  tff(c_1745, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1741])).
% 7.80/2.89  tff(c_1753, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_1745])).
% 7.80/2.89  tff(c_1754, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_1753])).
% 7.80/2.89  tff(c_16, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.80/2.89  tff(c_73, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_partfun1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 7.80/2.89  tff(c_1762, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1754, c_73])).
% 7.80/2.89  tff(c_1769, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_70, c_54, c_1762])).
% 7.80/2.89  tff(c_1793, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1769, c_78])).
% 7.80/2.89  tff(c_1811, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1793])).
% 7.80/2.89  tff(c_634, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_630])).
% 7.80/2.89  tff(c_642, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_634])).
% 7.80/2.89  tff(c_643, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_642])).
% 7.80/2.89  tff(c_653, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_643, c_74])).
% 7.80/2.89  tff(c_663, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_70, c_54, c_653])).
% 7.80/2.89  tff(c_18, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_relat_1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.80/2.89  tff(c_72, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_partfun1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_18])).
% 7.80/2.89  tff(c_677, plain, (![B_11]: (k2_funct_1('#skF_3')=B_11 | k5_relat_1(B_11, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_11)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_663, c_72])).
% 7.80/2.89  tff(c_703, plain, (![B_11]: (k2_funct_1('#skF_3')=B_11 | k5_relat_1(B_11, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_11)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_70, c_54, c_677])).
% 7.80/2.89  tff(c_3889, plain, (![B_294]: (k2_funct_1('#skF_3')=B_294 | k5_relat_1(B_294, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_294)!='#skF_1' | ~v1_funct_1(B_294) | ~v1_relat_1(B_294))), inference(demodulation, [status(thm), theory('equality')], [c_1811, c_703])).
% 7.80/2.89  tff(c_3979, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_132, c_3889])).
% 7.80/2.89  tff(c_4074, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1703, c_3979])).
% 7.80/2.89  tff(c_4075, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_4074])).
% 7.80/2.89  tff(c_689, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_663, c_78])).
% 7.80/2.89  tff(c_706, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_689])).
% 7.80/2.89  tff(c_584, plain, (![E_121, A_124, B_122, F_120, D_123, C_119]: (k1_partfun1(A_124, B_122, C_119, D_123, E_121, F_120)=k5_relat_1(E_121, F_120) | ~m1_subset_1(F_120, k1_zfmisc_1(k2_zfmisc_1(C_119, D_123))) | ~v1_funct_1(F_120) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_1(E_121))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.80/2.89  tff(c_590, plain, (![A_124, B_122, E_121]: (k1_partfun1(A_124, B_122, '#skF_2', '#skF_1', E_121, '#skF_4')=k5_relat_1(E_121, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_1(E_121))), inference(resolution, [status(thm)], [c_60, c_584])).
% 7.80/2.89  tff(c_1708, plain, (![A_187, B_188, E_189]: (k1_partfun1(A_187, B_188, '#skF_2', '#skF_1', E_189, '#skF_4')=k5_relat_1(E_189, '#skF_4') | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1(E_189))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_590])).
% 7.80/2.89  tff(c_1714, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1708])).
% 7.80/2.89  tff(c_1721, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_515, c_1714])).
% 7.80/2.89  tff(c_1186, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_647])).
% 7.80/2.89  tff(c_1747, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1741])).
% 7.80/2.89  tff(c_1757, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1186, c_1641, c_1747])).
% 7.80/2.89  tff(c_1758, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_1757])).
% 7.80/2.89  tff(c_1824, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1758, c_73])).
% 7.80/2.89  tff(c_1831, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_64, c_1641, c_1824])).
% 7.80/2.89  tff(c_1857, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1831, c_78])).
% 7.80/2.89  tff(c_1872, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1857])).
% 7.80/2.89  tff(c_1671, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k5_relat_1(B_11, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1657, c_72])).
% 7.80/2.89  tff(c_1700, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k5_relat_1(B_11, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_64, c_1641, c_1671])).
% 7.80/2.89  tff(c_5026, plain, (![B_340]: (k2_funct_1('#skF_4')=B_340 | k5_relat_1(B_340, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_340)!='#skF_2' | ~v1_funct_1(B_340) | ~v1_relat_1(B_340))), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_1700])).
% 7.80/2.89  tff(c_5167, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_5026])).
% 7.80/2.89  tff(c_5290, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_706, c_1721, c_5167])).
% 7.80/2.89  tff(c_5295, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5290, c_1758])).
% 7.80/2.89  tff(c_5298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4075, c_5295])).
% 7.80/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.89  
% 7.80/2.89  Inference rules
% 7.80/2.89  ----------------------
% 7.80/2.89  #Ref     : 0
% 7.80/2.89  #Sup     : 1049
% 7.80/2.89  #Fact    : 0
% 7.80/2.89  #Define  : 0
% 7.80/2.89  #Split   : 25
% 7.80/2.89  #Chain   : 0
% 7.80/2.89  #Close   : 0
% 7.80/2.89  
% 7.80/2.89  Ordering : KBO
% 7.80/2.89  
% 7.80/2.90  Simplification rules
% 7.80/2.90  ----------------------
% 7.80/2.90  #Subsume      : 74
% 7.80/2.90  #Demod        : 2141
% 7.80/2.90  #Tautology    : 279
% 7.80/2.90  #SimpNegUnit  : 133
% 7.80/2.90  #BackRed      : 20
% 7.80/2.90  
% 7.80/2.90  #Partial instantiations: 0
% 7.80/2.90  #Strategies tried      : 1
% 7.80/2.90  
% 7.80/2.90  Timing (in seconds)
% 7.80/2.90  ----------------------
% 7.80/2.90  Preprocessing        : 0.37
% 7.80/2.90  Parsing              : 0.19
% 7.80/2.90  CNF conversion       : 0.03
% 7.80/2.90  Main loop            : 1.74
% 7.80/2.90  Inferencing          : 0.48
% 7.80/2.90  Reduction            : 0.84
% 7.80/2.90  Demodulation         : 0.69
% 7.80/2.90  BG Simplification    : 0.05
% 7.80/2.90  Subsumption          : 0.28
% 7.80/2.90  Abstraction          : 0.07
% 7.80/2.90  MUC search           : 0.00
% 7.80/2.90  Cooper               : 0.00
% 7.80/2.90  Total                : 2.16
% 7.80/2.90  Index Insertion      : 0.00
% 7.80/2.90  Index Deletion       : 0.00
% 7.80/2.90  Index Matching       : 0.00
% 7.80/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
