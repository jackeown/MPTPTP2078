%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:19 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 274 expanded)
%              Number of leaves         :   40 ( 115 expanded)
%              Depth                    :   11
%              Number of atoms          :  235 (1123 expanded)
%              Number of equality atoms :   95 ( 395 expanded)
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

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_146,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

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

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_144,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_134,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_56,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_147,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_160,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_147])).

tff(c_238,plain,(
    ! [B_72,A_73,C_74] :
      ( k1_xboole_0 = B_72
      | k1_relset_1(A_73,B_72,C_74) = A_73
      | ~ v1_funct_2(C_74,A_73,B_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_247,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_238])).

tff(c_256,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_160,c_247])).

tff(c_257,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_256])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_117,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_117])).

tff(c_135,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_126])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_123,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_117])).

tff(c_132,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_159,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_147])).

tff(c_244,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_238])).

tff(c_252,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_159,c_244])).

tff(c_253,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_252])).

tff(c_50,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_20,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_relat_1(k1_relat_1(A_12)) != k5_relat_1(A_12,B_14)
      | k2_relat_1(A_12) != k1_relat_1(B_14)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_364,plain,(
    ! [A_91,B_92] :
      ( k2_funct_1(A_91) = B_92
      | k6_partfun1(k1_relat_1(A_91)) != k5_relat_1(A_91,B_92)
      | k2_relat_1(A_91) != k1_relat_1(B_92)
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_20])).

tff(c_368,plain,(
    ! [B_92] :
      ( k2_funct_1('#skF_3') = B_92
      | k5_relat_1('#skF_3',B_92) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_92)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_364])).

tff(c_381,plain,(
    ! [B_93] :
      ( k2_funct_1('#skF_3') = B_93
      | k5_relat_1('#skF_3',B_93) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_93)
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_78,c_62,c_368])).

tff(c_387,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_135,c_381])).

tff(c_398,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_257,c_387])).

tff(c_399,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_398])).

tff(c_404,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_519,plain,(
    ! [B_129,C_130,A_131] :
      ( k6_partfun1(B_129) = k5_relat_1(k2_funct_1(C_130),C_130)
      | k1_xboole_0 = B_129
      | ~ v2_funct_1(C_130)
      | k2_relset_1(A_131,B_129,C_130) != B_129
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_129)))
      | ~ v1_funct_2(C_130,A_131,B_129)
      | ~ v1_funct_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_523,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_519])).

tff(c_529,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_62,c_523])).

tff(c_530,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_529])).

tff(c_18,plain,(
    ! [A_11] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_11),A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_538,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_18])).

tff(c_545,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_78,c_62,c_82,c_538])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_545])).

tff(c_548,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_634,plain,(
    ! [A_152,C_151,F_150,E_148,D_153,B_149] :
      ( k1_partfun1(A_152,B_149,C_151,D_153,E_148,F_150) = k5_relat_1(E_148,F_150)
      | ~ m1_subset_1(F_150,k1_zfmisc_1(k2_zfmisc_1(C_151,D_153)))
      | ~ v1_funct_1(F_150)
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1(A_152,B_149)))
      | ~ v1_funct_1(E_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_640,plain,(
    ! [A_152,B_149,E_148] :
      ( k1_partfun1(A_152,B_149,'#skF_2','#skF_1',E_148,'#skF_4') = k5_relat_1(E_148,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1(A_152,B_149)))
      | ~ v1_funct_1(E_148) ) ),
    inference(resolution,[status(thm)],[c_68,c_634])).

tff(c_676,plain,(
    ! [A_158,B_159,E_160] :
      ( k1_partfun1(A_158,B_159,'#skF_2','#skF_1',E_160,'#skF_4') = k5_relat_1(E_160,'#skF_4')
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_1(E_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_640])).

tff(c_682,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_676])).

tff(c_689,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_682])).

tff(c_46,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_340,plain,(
    ! [D_87,C_88,A_89,B_90] :
      ( D_87 = C_88
      | ~ r2_relset_1(A_89,B_90,C_88,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_348,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_340])).

tff(c_363,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_348])).

tff(c_555,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_363])).

tff(c_694,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_555])).

tff(c_804,plain,(
    ! [D_184,B_188,A_185,E_189,F_187,C_186] :
      ( m1_subset_1(k1_partfun1(A_185,B_188,C_186,D_184,E_189,F_187),k1_zfmisc_1(k2_zfmisc_1(A_185,D_184)))
      | ~ m1_subset_1(F_187,k1_zfmisc_1(k2_zfmisc_1(C_186,D_184)))
      | ~ v1_funct_1(F_187)
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_185,B_188)))
      | ~ v1_funct_1(E_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_858,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_804])).

tff(c_887,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_858])).

tff(c_889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_694,c_887])).

tff(c_890,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_363])).

tff(c_987,plain,(
    ! [C_211,B_209,F_210,E_208,D_213,A_212] :
      ( k1_partfun1(A_212,B_209,C_211,D_213,E_208,F_210) = k5_relat_1(E_208,F_210)
      | ~ m1_subset_1(F_210,k1_zfmisc_1(k2_zfmisc_1(C_211,D_213)))
      | ~ v1_funct_1(F_210)
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_212,B_209)))
      | ~ v1_funct_1(E_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_993,plain,(
    ! [A_212,B_209,E_208] :
      ( k1_partfun1(A_212,B_209,'#skF_2','#skF_1',E_208,'#skF_4') = k5_relat_1(E_208,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_212,B_209)))
      | ~ v1_funct_1(E_208) ) ),
    inference(resolution,[status(thm)],[c_68,c_987])).

tff(c_1041,plain,(
    ! [A_218,B_219,E_220] :
      ( k1_partfun1(A_218,B_219,'#skF_2','#skF_1',E_220,'#skF_4') = k5_relat_1(E_220,'#skF_4')
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | ~ v1_funct_1(E_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_993])).

tff(c_1047,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1041])).

tff(c_1054,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_890,c_1047])).

tff(c_1056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_548,c_1054])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:54:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.70  
% 4.07/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.71  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.07/1.71  
% 4.07/1.71  %Foreground sorts:
% 4.07/1.71  
% 4.07/1.71  
% 4.07/1.71  %Background operators:
% 4.07/1.71  
% 4.07/1.71  
% 4.07/1.71  %Foreground operators:
% 4.07/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.07/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.07/1.71  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.07/1.71  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.71  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.07/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.07/1.71  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.07/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.07/1.71  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.07/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.07/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.07/1.71  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.07/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.07/1.71  tff('#skF_1', type, '#skF_1': $i).
% 4.07/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.07/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.07/1.71  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.07/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.07/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.07/1.71  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.07/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.07/1.71  
% 4.07/1.73  tff(f_188, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.07/1.73  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.07/1.73  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.07/1.73  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.07/1.73  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.07/1.73  tff(f_146, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.07/1.73  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.07/1.73  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.07/1.73  tff(f_162, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 4.07/1.73  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 4.07/1.73  tff(f_144, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.07/1.73  tff(f_134, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.07/1.73  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.07/1.73  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.07/1.73  tff(c_56, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_60, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_147, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.07/1.73  tff(c_160, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_147])).
% 4.07/1.73  tff(c_238, plain, (![B_72, A_73, C_74]: (k1_xboole_0=B_72 | k1_relset_1(A_73, B_72, C_74)=A_73 | ~v1_funct_2(C_74, A_73, B_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.07/1.73  tff(c_247, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_238])).
% 4.07/1.73  tff(c_256, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_160, c_247])).
% 4.07/1.73  tff(c_257, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_60, c_256])).
% 4.07/1.73  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.07/1.73  tff(c_117, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.07/1.73  tff(c_126, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_117])).
% 4.07/1.73  tff(c_135, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_126])).
% 4.07/1.73  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_123, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_117])).
% 4.07/1.73  tff(c_132, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_123])).
% 4.07/1.73  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_159, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_147])).
% 4.07/1.73  tff(c_244, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_238])).
% 4.07/1.73  tff(c_252, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_159, c_244])).
% 4.07/1.73  tff(c_253, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_252])).
% 4.07/1.73  tff(c_50, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.07/1.73  tff(c_20, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_relat_1(k1_relat_1(A_12))!=k5_relat_1(A_12, B_14) | k2_relat_1(A_12)!=k1_relat_1(B_14) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.07/1.73  tff(c_364, plain, (![A_91, B_92]: (k2_funct_1(A_91)=B_92 | k6_partfun1(k1_relat_1(A_91))!=k5_relat_1(A_91, B_92) | k2_relat_1(A_91)!=k1_relat_1(B_92) | ~v2_funct_1(A_91) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_20])).
% 4.07/1.73  tff(c_368, plain, (![B_92]: (k2_funct_1('#skF_3')=B_92 | k5_relat_1('#skF_3', B_92)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_92) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_253, c_364])).
% 4.07/1.73  tff(c_381, plain, (![B_93]: (k2_funct_1('#skF_3')=B_93 | k5_relat_1('#skF_3', B_93)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_93) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_78, c_62, c_368])).
% 4.07/1.73  tff(c_387, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_135, c_381])).
% 4.07/1.73  tff(c_398, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_257, c_387])).
% 4.07/1.73  tff(c_399, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_398])).
% 4.07/1.73  tff(c_404, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_399])).
% 4.07/1.73  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.07/1.73  tff(c_82, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6])).
% 4.07/1.73  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_519, plain, (![B_129, C_130, A_131]: (k6_partfun1(B_129)=k5_relat_1(k2_funct_1(C_130), C_130) | k1_xboole_0=B_129 | ~v2_funct_1(C_130) | k2_relset_1(A_131, B_129, C_130)!=B_129 | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_129))) | ~v1_funct_2(C_130, A_131, B_129) | ~v1_funct_1(C_130))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.07/1.73  tff(c_523, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_519])).
% 4.07/1.73  tff(c_529, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_62, c_523])).
% 4.07/1.73  tff(c_530, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_529])).
% 4.07/1.73  tff(c_18, plain, (![A_11]: (k1_relat_1(k5_relat_1(k2_funct_1(A_11), A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.07/1.73  tff(c_538, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_530, c_18])).
% 4.07/1.73  tff(c_545, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_78, c_62, c_82, c_538])).
% 4.07/1.73  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_404, c_545])).
% 4.07/1.73  tff(c_548, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_399])).
% 4.07/1.73  tff(c_634, plain, (![A_152, C_151, F_150, E_148, D_153, B_149]: (k1_partfun1(A_152, B_149, C_151, D_153, E_148, F_150)=k5_relat_1(E_148, F_150) | ~m1_subset_1(F_150, k1_zfmisc_1(k2_zfmisc_1(C_151, D_153))) | ~v1_funct_1(F_150) | ~m1_subset_1(E_148, k1_zfmisc_1(k2_zfmisc_1(A_152, B_149))) | ~v1_funct_1(E_148))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.07/1.73  tff(c_640, plain, (![A_152, B_149, E_148]: (k1_partfun1(A_152, B_149, '#skF_2', '#skF_1', E_148, '#skF_4')=k5_relat_1(E_148, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_148, k1_zfmisc_1(k2_zfmisc_1(A_152, B_149))) | ~v1_funct_1(E_148))), inference(resolution, [status(thm)], [c_68, c_634])).
% 4.07/1.73  tff(c_676, plain, (![A_158, B_159, E_160]: (k1_partfun1(A_158, B_159, '#skF_2', '#skF_1', E_160, '#skF_4')=k5_relat_1(E_160, '#skF_4') | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_1(E_160))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_640])).
% 4.07/1.73  tff(c_682, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_676])).
% 4.07/1.73  tff(c_689, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_682])).
% 4.07/1.73  tff(c_46, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.07/1.73  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.07/1.73  tff(c_340, plain, (![D_87, C_88, A_89, B_90]: (D_87=C_88 | ~r2_relset_1(A_89, B_90, C_88, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.73  tff(c_348, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_340])).
% 4.07/1.73  tff(c_363, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_348])).
% 4.07/1.73  tff(c_555, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_363])).
% 4.07/1.73  tff(c_694, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_555])).
% 4.07/1.73  tff(c_804, plain, (![D_184, B_188, A_185, E_189, F_187, C_186]: (m1_subset_1(k1_partfun1(A_185, B_188, C_186, D_184, E_189, F_187), k1_zfmisc_1(k2_zfmisc_1(A_185, D_184))) | ~m1_subset_1(F_187, k1_zfmisc_1(k2_zfmisc_1(C_186, D_184))) | ~v1_funct_1(F_187) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_185, B_188))) | ~v1_funct_1(E_189))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.07/1.73  tff(c_858, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_689, c_804])).
% 4.07/1.73  tff(c_887, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_858])).
% 4.07/1.73  tff(c_889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_694, c_887])).
% 4.07/1.73  tff(c_890, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_363])).
% 4.07/1.73  tff(c_987, plain, (![C_211, B_209, F_210, E_208, D_213, A_212]: (k1_partfun1(A_212, B_209, C_211, D_213, E_208, F_210)=k5_relat_1(E_208, F_210) | ~m1_subset_1(F_210, k1_zfmisc_1(k2_zfmisc_1(C_211, D_213))) | ~v1_funct_1(F_210) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_212, B_209))) | ~v1_funct_1(E_208))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.07/1.73  tff(c_993, plain, (![A_212, B_209, E_208]: (k1_partfun1(A_212, B_209, '#skF_2', '#skF_1', E_208, '#skF_4')=k5_relat_1(E_208, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_212, B_209))) | ~v1_funct_1(E_208))), inference(resolution, [status(thm)], [c_68, c_987])).
% 4.07/1.73  tff(c_1041, plain, (![A_218, B_219, E_220]: (k1_partfun1(A_218, B_219, '#skF_2', '#skF_1', E_220, '#skF_4')=k5_relat_1(E_220, '#skF_4') | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | ~v1_funct_1(E_220))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_993])).
% 4.07/1.73  tff(c_1047, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1041])).
% 4.07/1.73  tff(c_1054, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_890, c_1047])).
% 4.07/1.73  tff(c_1056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_548, c_1054])).
% 4.07/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.73  
% 4.07/1.73  Inference rules
% 4.07/1.73  ----------------------
% 4.07/1.73  #Ref     : 0
% 4.07/1.73  #Sup     : 206
% 4.07/1.73  #Fact    : 0
% 4.07/1.73  #Define  : 0
% 4.07/1.73  #Split   : 8
% 4.07/1.73  #Chain   : 0
% 4.07/1.73  #Close   : 0
% 4.07/1.73  
% 4.07/1.73  Ordering : KBO
% 4.07/1.73  
% 4.07/1.73  Simplification rules
% 4.07/1.73  ----------------------
% 4.07/1.73  #Subsume      : 12
% 4.07/1.73  #Demod        : 178
% 4.07/1.73  #Tautology    : 74
% 4.07/1.73  #SimpNegUnit  : 17
% 4.07/1.73  #BackRed      : 14
% 4.07/1.73  
% 4.07/1.73  #Partial instantiations: 0
% 4.07/1.73  #Strategies tried      : 1
% 4.07/1.73  
% 4.07/1.73  Timing (in seconds)
% 4.07/1.73  ----------------------
% 4.07/1.73  Preprocessing        : 0.41
% 4.07/1.73  Parsing              : 0.22
% 4.07/1.73  CNF conversion       : 0.03
% 4.07/1.73  Main loop            : 0.50
% 4.07/1.73  Inferencing          : 0.18
% 4.07/1.73  Reduction            : 0.17
% 4.07/1.73  Demodulation         : 0.12
% 4.07/1.73  BG Simplification    : 0.03
% 4.07/1.73  Subsumption          : 0.09
% 4.07/1.73  Abstraction          : 0.02
% 4.07/1.73  MUC search           : 0.00
% 4.07/1.73  Cooper               : 0.00
% 4.07/1.73  Total                : 0.94
% 4.07/1.73  Index Insertion      : 0.00
% 4.07/1.73  Index Deletion       : 0.00
% 4.07/1.73  Index Matching       : 0.00
% 4.07/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
