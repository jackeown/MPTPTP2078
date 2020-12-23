%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:02 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 631 expanded)
%              Number of leaves         :   40 ( 242 expanded)
%              Depth                    :   18
%              Number of atoms          :  296 (2698 expanded)
%              Number of equality atoms :  108 (1002 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_178,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_135,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
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

tff(f_93,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_152,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_133,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_46,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_91,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_165,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_177,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_165])).

tff(c_241,plain,(
    ! [B_76,A_77,C_78] :
      ( k1_xboole_0 = B_76
      | k1_relset_1(A_77,B_76,C_78) = A_77
      | ~ v1_funct_2(C_78,A_77,B_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_250,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_241])).

tff(c_259,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_177,c_250])).

tff(c_260,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_259])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_103,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_91])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_176,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_165])).

tff(c_247,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_241])).

tff(c_255,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_176,c_247])).

tff(c_256,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_255])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_133,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_relset_1(A_57,B_58,C_59) = k2_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_139,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_133])).

tff(c_145,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_139])).

tff(c_44,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_10,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_relat_1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_499,plain,(
    ! [A_122,B_123] :
      ( k2_funct_1(A_122) = B_123
      | k6_partfun1(k2_relat_1(A_122)) != k5_relat_1(B_123,A_122)
      | k2_relat_1(B_123) != k1_relat_1(A_122)
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_501,plain,(
    ! [B_123] :
      ( k2_funct_1('#skF_3') = B_123
      | k5_relat_1(B_123,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_123) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_499])).

tff(c_504,plain,(
    ! [B_124] :
      ( k2_funct_1('#skF_3') = B_124
      | k5_relat_1(B_124,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_124) != '#skF_1'
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_70,c_54,c_256,c_501])).

tff(c_507,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_504])).

tff(c_516,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_507])).

tff(c_517,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_516])).

tff(c_522,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_24,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_71,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_24])).

tff(c_122,plain,(
    ! [A_53,B_54,D_55] :
      ( r2_relset_1(A_53,B_54,D_55,D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_129,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_71,c_122])).

tff(c_146,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_133])).

tff(c_429,plain,(
    ! [E_121,D_116,A_118,C_120,F_119,B_117] :
      ( m1_subset_1(k1_partfun1(A_118,B_117,C_120,D_116,E_121,F_119),k1_zfmisc_1(k2_zfmisc_1(A_118,D_116)))
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_120,D_116)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117)))
      | ~ v1_funct_1(E_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_286,plain,(
    ! [D_84,C_85,A_86,B_87] :
      ( D_84 = C_85
      | ~ r2_relset_1(A_86,B_87,C_85,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_294,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_286])).

tff(c_309,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_294])).

tff(c_310,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_445,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_429,c_310])).

tff(c_489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_445])).

tff(c_490,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_848,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k2_relset_1(A_156,B_157,C_158) = B_157
      | ~ r2_relset_1(B_157,B_157,k1_partfun1(B_157,A_156,A_156,B_157,D_159,C_158),k6_partfun1(B_157))
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(B_157,A_156)))
      | ~ v1_funct_2(D_159,B_157,A_156)
      | ~ v1_funct_1(D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_funct_2(C_158,A_156,B_157)
      | ~ v1_funct_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_851,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_848])).

tff(c_853,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_129,c_146,c_851])).

tff(c_855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_522,c_853])).

tff(c_857,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_72,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_partfun1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_861,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_72])).

tff(c_865,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_64,c_260,c_861])).

tff(c_873,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_865])).

tff(c_4,plain,(
    ! [A_1] : v2_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_1] : v2_funct_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4])).

tff(c_888,plain,(
    ! [C_170,D_172,A_171,E_167,B_168,F_169] :
      ( k1_partfun1(A_171,B_168,C_170,D_172,E_167,F_169) = k5_relat_1(E_167,F_169)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(C_170,D_172)))
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_171,B_168)))
      | ~ v1_funct_1(E_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_894,plain,(
    ! [A_171,B_168,E_167] :
      ( k1_partfun1(A_171,B_168,'#skF_2','#skF_1',E_167,'#skF_4') = k5_relat_1(E_167,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_171,B_168)))
      | ~ v1_funct_1(E_167) ) ),
    inference(resolution,[status(thm)],[c_60,c_888])).

tff(c_1001,plain,(
    ! [A_187,B_188,E_189] :
      ( k1_partfun1(A_187,B_188,'#skF_2','#skF_1',E_189,'#skF_4') = k5_relat_1(E_189,'#skF_4')
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(E_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_894])).

tff(c_1010,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1001])).

tff(c_1018,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_490,c_1010])).

tff(c_6,plain,(
    ! [A_2,B_4] :
      ( v2_funct_1(A_2)
      | k2_relat_1(B_4) != k1_relat_1(A_2)
      | ~ v2_funct_1(k5_relat_1(B_4,A_2))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1028,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1018,c_6])).

tff(c_1034,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_64,c_103,c_70,c_73,c_145,c_260,c_1028])).

tff(c_1036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_873,c_1034])).

tff(c_1038,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_865])).

tff(c_1039,plain,(
    ! [B_190] :
      ( k2_funct_1('#skF_4') = B_190
      | k5_relat_1(B_190,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_190) != '#skF_2'
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190) ) ),
    inference(splitRight,[status(thm)],[c_865])).

tff(c_1045,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_1039])).

tff(c_1054,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_145,c_1045])).

tff(c_1056,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1054])).

tff(c_1072,plain,(
    ! [A_202,B_199,E_198,D_203,C_201,F_200] :
      ( k1_partfun1(A_202,B_199,C_201,D_203,E_198,F_200) = k5_relat_1(E_198,F_200)
      | ~ m1_subset_1(F_200,k1_zfmisc_1(k2_zfmisc_1(C_201,D_203)))
      | ~ v1_funct_1(F_200)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_202,B_199)))
      | ~ v1_funct_1(E_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1078,plain,(
    ! [A_202,B_199,E_198] :
      ( k1_partfun1(A_202,B_199,'#skF_2','#skF_1',E_198,'#skF_4') = k5_relat_1(E_198,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_202,B_199)))
      | ~ v1_funct_1(E_198) ) ),
    inference(resolution,[status(thm)],[c_60,c_1072])).

tff(c_1393,plain,(
    ! [A_225,B_226,E_227] :
      ( k1_partfun1(A_225,B_226,'#skF_2','#skF_1',E_227,'#skF_4') = k5_relat_1(E_227,'#skF_4')
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226)))
      | ~ v1_funct_1(E_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1078])).

tff(c_1408,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1393])).

tff(c_1422,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_490,c_1408])).

tff(c_1424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1056,c_1422])).

tff(c_1425,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_12,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1431,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_12])).

tff(c_1435,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_64,c_1038,c_1431])).

tff(c_1437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:32:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.96  
% 4.35/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.96  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.35/1.96  
% 4.35/1.96  %Foreground sorts:
% 4.35/1.96  
% 4.35/1.96  
% 4.35/1.96  %Background operators:
% 4.35/1.96  
% 4.35/1.96  
% 4.35/1.96  %Foreground operators:
% 4.35/1.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.35/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.35/1.96  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.35/1.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.35/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.96  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.35/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.35/1.96  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.35/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.35/1.96  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.35/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.35/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.35/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.35/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.35/1.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.35/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.35/1.96  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.35/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.35/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.35/1.96  tff('#skF_4', type, '#skF_4': $i).
% 4.35/1.96  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.35/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.35/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.35/1.96  
% 4.67/1.99  tff(f_178, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.67/1.99  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.67/1.99  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.67/1.99  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.67/1.99  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.67/1.99  tff(f_135, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.67/1.99  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 4.67/1.99  tff(f_93, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.67/1.99  tff(f_91, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.67/1.99  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.67/1.99  tff(f_152, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.67/1.99  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.67/1.99  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.67/1.99  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 4.67/1.99  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 4.67/1.99  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_91, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.67/1.99  tff(c_104, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_91])).
% 4.67/1.99  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_165, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.67/1.99  tff(c_177, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_165])).
% 4.67/1.99  tff(c_241, plain, (![B_76, A_77, C_78]: (k1_xboole_0=B_76 | k1_relset_1(A_77, B_76, C_78)=A_77 | ~v1_funct_2(C_78, A_77, B_76) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.67/1.99  tff(c_250, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_241])).
% 4.67/1.99  tff(c_259, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_177, c_250])).
% 4.67/1.99  tff(c_260, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_259])).
% 4.67/1.99  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_103, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_91])).
% 4.67/1.99  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_176, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_165])).
% 4.67/1.99  tff(c_247, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_241])).
% 4.67/1.99  tff(c_255, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_176, c_247])).
% 4.67/1.99  tff(c_256, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_255])).
% 4.67/1.99  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_133, plain, (![A_57, B_58, C_59]: (k2_relset_1(A_57, B_58, C_59)=k2_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.67/1.99  tff(c_139, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_133])).
% 4.67/1.99  tff(c_145, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_139])).
% 4.67/1.99  tff(c_44, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.67/1.99  tff(c_10, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.67/1.99  tff(c_499, plain, (![A_122, B_123]: (k2_funct_1(A_122)=B_123 | k6_partfun1(k2_relat_1(A_122))!=k5_relat_1(B_123, A_122) | k2_relat_1(B_123)!=k1_relat_1(A_122) | ~v2_funct_1(A_122) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 4.67/1.99  tff(c_501, plain, (![B_123]: (k2_funct_1('#skF_3')=B_123 | k5_relat_1(B_123, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_123)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_123) | ~v1_relat_1(B_123) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_499])).
% 4.67/1.99  tff(c_504, plain, (![B_124]: (k2_funct_1('#skF_3')=B_124 | k5_relat_1(B_124, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_124)!='#skF_1' | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_70, c_54, c_256, c_501])).
% 4.67/1.99  tff(c_507, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_104, c_504])).
% 4.67/1.99  tff(c_516, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_507])).
% 4.67/1.99  tff(c_517, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_48, c_516])).
% 4.67/1.99  tff(c_522, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_517])).
% 4.67/1.99  tff(c_24, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.67/1.99  tff(c_71, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_24])).
% 4.67/1.99  tff(c_122, plain, (![A_53, B_54, D_55]: (r2_relset_1(A_53, B_54, D_55, D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.67/1.99  tff(c_129, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_71, c_122])).
% 4.67/1.99  tff(c_146, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_133])).
% 4.67/1.99  tff(c_429, plain, (![E_121, D_116, A_118, C_120, F_119, B_117]: (m1_subset_1(k1_partfun1(A_118, B_117, C_120, D_116, E_121, F_119), k1_zfmisc_1(k2_zfmisc_1(A_118, D_116))) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_120, D_116))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))) | ~v1_funct_1(E_121))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.67/1.99  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.67/1.99  tff(c_286, plain, (![D_84, C_85, A_86, B_87]: (D_84=C_85 | ~r2_relset_1(A_86, B_87, C_85, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.67/1.99  tff(c_294, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_286])).
% 4.67/1.99  tff(c_309, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_294])).
% 4.67/1.99  tff(c_310, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_309])).
% 4.67/1.99  tff(c_445, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_429, c_310])).
% 4.67/1.99  tff(c_489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_445])).
% 4.67/1.99  tff(c_490, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_309])).
% 4.67/1.99  tff(c_848, plain, (![A_156, B_157, C_158, D_159]: (k2_relset_1(A_156, B_157, C_158)=B_157 | ~r2_relset_1(B_157, B_157, k1_partfun1(B_157, A_156, A_156, B_157, D_159, C_158), k6_partfun1(B_157)) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(B_157, A_156))) | ~v1_funct_2(D_159, B_157, A_156) | ~v1_funct_1(D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_2(C_158, A_156, B_157) | ~v1_funct_1(C_158))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.67/1.99  tff(c_851, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_490, c_848])).
% 4.67/1.99  tff(c_853, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_129, c_146, c_851])).
% 4.67/1.99  tff(c_855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_522, c_853])).
% 4.67/1.99  tff(c_857, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_517])).
% 4.67/1.99  tff(c_72, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_partfun1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 4.67/1.99  tff(c_861, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_857, c_72])).
% 4.67/1.99  tff(c_865, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_64, c_260, c_861])).
% 4.67/1.99  tff(c_873, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_865])).
% 4.67/1.99  tff(c_4, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.67/1.99  tff(c_73, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4])).
% 4.67/1.99  tff(c_888, plain, (![C_170, D_172, A_171, E_167, B_168, F_169]: (k1_partfun1(A_171, B_168, C_170, D_172, E_167, F_169)=k5_relat_1(E_167, F_169) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(C_170, D_172))) | ~v1_funct_1(F_169) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_171, B_168))) | ~v1_funct_1(E_167))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.67/1.99  tff(c_894, plain, (![A_171, B_168, E_167]: (k1_partfun1(A_171, B_168, '#skF_2', '#skF_1', E_167, '#skF_4')=k5_relat_1(E_167, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_171, B_168))) | ~v1_funct_1(E_167))), inference(resolution, [status(thm)], [c_60, c_888])).
% 4.67/1.99  tff(c_1001, plain, (![A_187, B_188, E_189]: (k1_partfun1(A_187, B_188, '#skF_2', '#skF_1', E_189, '#skF_4')=k5_relat_1(E_189, '#skF_4') | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1(E_189))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_894])).
% 4.67/1.99  tff(c_1010, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1001])).
% 4.67/1.99  tff(c_1018, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_490, c_1010])).
% 4.67/1.99  tff(c_6, plain, (![A_2, B_4]: (v2_funct_1(A_2) | k2_relat_1(B_4)!=k1_relat_1(A_2) | ~v2_funct_1(k5_relat_1(B_4, A_2)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.67/1.99  tff(c_1028, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1018, c_6])).
% 4.67/1.99  tff(c_1034, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_64, c_103, c_70, c_73, c_145, c_260, c_1028])).
% 4.67/1.99  tff(c_1036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_873, c_1034])).
% 4.67/1.99  tff(c_1038, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_865])).
% 4.67/1.99  tff(c_1039, plain, (![B_190]: (k2_funct_1('#skF_4')=B_190 | k5_relat_1(B_190, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_190)!='#skF_2' | ~v1_funct_1(B_190) | ~v1_relat_1(B_190))), inference(splitRight, [status(thm)], [c_865])).
% 4.67/1.99  tff(c_1045, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_1039])).
% 4.67/1.99  tff(c_1054, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_145, c_1045])).
% 4.67/1.99  tff(c_1056, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1054])).
% 4.67/1.99  tff(c_1072, plain, (![A_202, B_199, E_198, D_203, C_201, F_200]: (k1_partfun1(A_202, B_199, C_201, D_203, E_198, F_200)=k5_relat_1(E_198, F_200) | ~m1_subset_1(F_200, k1_zfmisc_1(k2_zfmisc_1(C_201, D_203))) | ~v1_funct_1(F_200) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_202, B_199))) | ~v1_funct_1(E_198))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.67/1.99  tff(c_1078, plain, (![A_202, B_199, E_198]: (k1_partfun1(A_202, B_199, '#skF_2', '#skF_1', E_198, '#skF_4')=k5_relat_1(E_198, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_202, B_199))) | ~v1_funct_1(E_198))), inference(resolution, [status(thm)], [c_60, c_1072])).
% 4.67/1.99  tff(c_1393, plain, (![A_225, B_226, E_227]: (k1_partfun1(A_225, B_226, '#skF_2', '#skF_1', E_227, '#skF_4')=k5_relat_1(E_227, '#skF_4') | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))) | ~v1_funct_1(E_227))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1078])).
% 4.67/1.99  tff(c_1408, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1393])).
% 4.67/1.99  tff(c_1422, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_490, c_1408])).
% 4.67/1.99  tff(c_1424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1056, c_1422])).
% 4.67/1.99  tff(c_1425, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1054])).
% 4.67/1.99  tff(c_12, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.67/1.99  tff(c_1431, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1425, c_12])).
% 4.67/1.99  tff(c_1435, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_64, c_1038, c_1431])).
% 4.67/1.99  tff(c_1437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1435])).
% 4.67/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.99  
% 4.67/1.99  Inference rules
% 4.67/1.99  ----------------------
% 4.67/1.99  #Ref     : 0
% 4.67/1.99  #Sup     : 294
% 4.67/1.99  #Fact    : 0
% 4.67/1.99  #Define  : 0
% 4.67/1.99  #Split   : 15
% 4.67/1.99  #Chain   : 0
% 4.67/1.99  #Close   : 0
% 4.67/1.99  
% 4.67/1.99  Ordering : KBO
% 4.67/1.99  
% 4.67/1.99  Simplification rules
% 4.67/1.99  ----------------------
% 4.67/1.99  #Subsume      : 2
% 4.67/1.99  #Demod        : 226
% 4.67/1.99  #Tautology    : 74
% 4.67/1.99  #SimpNegUnit  : 19
% 4.67/1.99  #BackRed      : 10
% 4.67/1.99  
% 4.67/1.99  #Partial instantiations: 0
% 4.67/1.99  #Strategies tried      : 1
% 4.67/1.99  
% 4.67/1.99  Timing (in seconds)
% 4.67/1.99  ----------------------
% 4.67/1.99  Preprocessing        : 0.43
% 4.67/1.99  Parsing              : 0.25
% 4.67/1.99  CNF conversion       : 0.03
% 4.67/1.99  Main loop            : 0.67
% 4.67/1.99  Inferencing          : 0.25
% 4.67/1.99  Reduction            : 0.22
% 4.67/1.99  Demodulation         : 0.16
% 4.67/1.99  BG Simplification    : 0.03
% 4.67/1.99  Subsumption          : 0.11
% 4.67/1.99  Abstraction          : 0.03
% 4.67/1.99  MUC search           : 0.00
% 4.67/1.99  Cooper               : 0.00
% 4.67/1.99  Total                : 1.16
% 4.67/1.99  Index Insertion      : 0.00
% 4.67/1.99  Index Deletion       : 0.00
% 4.67/1.99  Index Matching       : 0.00
% 4.67/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
