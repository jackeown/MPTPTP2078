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
% DateTime   : Thu Dec  3 10:13:04 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :  112 (1064 expanded)
%              Number of leaves         :   38 ( 445 expanded)
%              Depth                    :   20
%              Number of atoms          :  317 (6374 expanded)
%              Number of equality atoms :   88 (1846 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( B != k1_xboole_0
       => ( k2_relset_1(A,B,C) = B
        <=> ! [D] :
              ( D != k1_xboole_0
             => ! [E] :
                  ( ( v1_funct_1(E)
                    & v1_funct_2(E,B,D)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) )
                 => ! [F] :
                      ( ( v1_funct_1(F)
                        & v1_funct_2(F,B,D)
                        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(B,D))) )
                     => ( r2_relset_1(A,D,k1_partfun1(A,B,B,D,C,E),k1_partfun1(A,B,B,D,C,F))
                       => r2_relset_1(B,D,E,F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
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

tff(f_81,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_56,plain,(
    k2_funct_1('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_76,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_62,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_66,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_50,plain,(
    ! [C_52,B_51,A_50] :
      ( m1_subset_1(k2_funct_1(C_52),k1_zfmisc_1(k2_zfmisc_1(B_51,A_50)))
      | k2_relset_1(A_50,B_51,C_52) != B_51
      | ~ v2_funct_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_2(C_52,A_50,B_51)
      | ~ v1_funct_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_213,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_funct_1(k2_funct_1(C_83))
      | k2_relset_1(A_84,B_85,C_83) != B_85
      | ~ v2_funct_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_funct_2(C_83,A_84,B_85)
      | ~ v1_funct_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_216,plain,
    ( v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_213])).

tff(c_222,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_66,c_216])).

tff(c_259,plain,(
    ! [C_92,B_93,A_94] :
      ( v1_funct_2(k2_funct_1(C_92),B_93,A_94)
      | k2_relset_1(A_94,B_93,C_92) != B_93
      | ~ v2_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93)))
      | ~ v1_funct_2(C_92,A_94,B_93)
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_262,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_259])).

tff(c_268,plain,(
    v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_66,c_262])).

tff(c_337,plain,(
    ! [C_110,B_111,A_112] :
      ( m1_subset_1(k2_funct_1(C_110),k1_zfmisc_1(k2_zfmisc_1(B_111,A_112)))
      | k2_relset_1(A_112,B_111,C_110) != B_111
      | ~ v2_funct_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111)))
      | ~ v1_funct_2(C_110,A_112,B_111)
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    ! [A_22,B_23,C_24] :
      ( v1_funct_1('#skF_3'(A_22,B_23,C_24))
      | k2_relset_1(A_22,B_23,C_24) = B_23
      | k1_xboole_0 = B_23
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_883,plain,(
    ! [B_177,A_178,C_179] :
      ( v1_funct_1('#skF_3'(B_177,A_178,k2_funct_1(C_179)))
      | k2_relset_1(B_177,A_178,k2_funct_1(C_179)) = A_178
      | k1_xboole_0 = A_178
      | ~ v1_funct_2(k2_funct_1(C_179),B_177,A_178)
      | ~ v1_funct_1(k2_funct_1(C_179))
      | k2_relset_1(A_178,B_177,C_179) != B_177
      | ~ v2_funct_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177)))
      | ~ v1_funct_2(C_179,A_178,B_177)
      | ~ v1_funct_1(C_179) ) ),
    inference(resolution,[status(thm)],[c_337,c_40])).

tff(c_895,plain,
    ( v1_funct_1('#skF_3'('#skF_5','#skF_4',k2_funct_1('#skF_6')))
    | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_883])).

tff(c_904,plain,
    ( v1_funct_1('#skF_3'('#skF_5','#skF_4',k2_funct_1('#skF_6')))
    | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_66,c_222,c_268,c_895])).

tff(c_905,plain,
    ( v1_funct_1('#skF_3'('#skF_5','#skF_4',k2_funct_1('#skF_6')))
    | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_904])).

tff(c_910,plain,(
    k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_905])).

tff(c_292,plain,(
    ! [D_99,F_101,A_103,B_100,C_98,E_102] :
      ( k1_partfun1(A_103,B_100,C_98,D_99,E_102,F_101) = k5_relat_1(E_102,F_101)
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(C_98,D_99)))
      | ~ v1_funct_1(F_101)
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_100)))
      | ~ v1_funct_1(E_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_294,plain,(
    ! [A_103,B_100,E_102] :
      ( k1_partfun1(A_103,B_100,'#skF_4','#skF_5',E_102,'#skF_6') = k5_relat_1(E_102,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_100)))
      | ~ v1_funct_1(E_102) ) ),
    inference(resolution,[status(thm)],[c_74,c_292])).

tff(c_299,plain,(
    ! [A_103,B_100,E_102] :
      ( k1_partfun1(A_103,B_100,'#skF_4','#skF_5',E_102,'#skF_6') = k5_relat_1(E_102,'#skF_6')
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_100)))
      | ~ v1_funct_1(E_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_294])).

tff(c_467,plain,(
    ! [B_130,A_131,C_132] :
      ( k1_partfun1(B_130,A_131,'#skF_4','#skF_5',k2_funct_1(C_132),'#skF_6') = k5_relat_1(k2_funct_1(C_132),'#skF_6')
      | ~ v1_funct_1(k2_funct_1(C_132))
      | k2_relset_1(A_131,B_130,C_132) != B_130
      | ~ v2_funct_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130)))
      | ~ v1_funct_2(C_132,A_131,B_130)
      | ~ v1_funct_1(C_132) ) ),
    inference(resolution,[status(thm)],[c_337,c_299])).

tff(c_473,plain,
    ( k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),'#skF_6') = k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_467])).

tff(c_480,plain,(
    k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),'#skF_6') = k5_relat_1(k2_funct_1('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_66,c_222,c_473])).

tff(c_942,plain,(
    ! [B_188,F_185,C_184,D_186,A_183,E_187] :
      ( r2_relset_1(B_188,D_186,E_187,F_185)
      | ~ r2_relset_1(A_183,D_186,k1_partfun1(A_183,B_188,B_188,D_186,C_184,E_187),k1_partfun1(A_183,B_188,B_188,D_186,C_184,F_185))
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1(B_188,D_186)))
      | ~ v1_funct_2(F_185,B_188,D_186)
      | ~ v1_funct_1(F_185)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(B_188,D_186)))
      | ~ v1_funct_2(E_187,B_188,D_186)
      | ~ v1_funct_1(E_187)
      | k1_xboole_0 = D_186
      | k2_relset_1(A_183,B_188,C_184) != B_188
      | k1_xboole_0 = B_188
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_188)))
      | ~ v1_funct_2(C_184,A_183,B_188)
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_948,plain,(
    ! [F_185] :
      ( r2_relset_1('#skF_4','#skF_5','#skF_6',F_185)
      | ~ r2_relset_1('#skF_5','#skF_5',k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),F_185))
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2(F_185,'#skF_4','#skF_5')
      | ~ v1_funct_1(F_185)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | k1_xboole_0 = '#skF_5'
      | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) != '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_942])).

tff(c_966,plain,(
    ! [F_185] :
      ( r2_relset_1('#skF_4','#skF_5','#skF_6',F_185)
      | ~ r2_relset_1('#skF_5','#skF_5',k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),F_185))
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2(F_185,'#skF_4','#skF_5')
      | ~ v1_funct_1(F_185)
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_268,c_910,c_78,c_76,c_74,c_948])).

tff(c_967,plain,(
    ! [F_185] :
      ( r2_relset_1('#skF_4','#skF_5','#skF_6',F_185)
      | ~ r2_relset_1('#skF_5','#skF_5',k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),F_185))
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2(F_185,'#skF_4','#skF_5')
      | ~ v1_funct_1(F_185)
      | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_966])).

tff(c_1007,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_1010,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_1007])).

tff(c_1014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_62,c_66,c_1010])).

tff(c_1016,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_94,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_94])).

tff(c_72,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_296,plain,(
    ! [A_103,B_100,E_102] :
      ( k1_partfun1(A_103,B_100,'#skF_5','#skF_4',E_102,'#skF_7') = k5_relat_1(E_102,'#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_100)))
      | ~ v1_funct_1(E_102) ) ),
    inference(resolution,[status(thm)],[c_68,c_292])).

tff(c_324,plain,(
    ! [A_107,B_108,E_109] :
      ( k1_partfun1(A_107,B_108,'#skF_5','#skF_4',E_109,'#skF_7') = k5_relat_1(E_109,'#skF_7')
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_1(E_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_296])).

tff(c_327,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_324])).

tff(c_333,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_327])).

tff(c_64,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k6_partfun1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_404,plain,(
    r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k6_partfun1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_64])).

tff(c_110,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_110])).

tff(c_149,plain,(
    ! [B_73,A_74,C_75] :
      ( k1_xboole_0 = B_73
      | k1_relset_1(A_74,B_73,C_75) = A_74
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_152,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_149])).

tff(c_158,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_117,c_152])).

tff(c_159,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_158])).

tff(c_28,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_relat_1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_partfun1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4])).

tff(c_26,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17] :
      ( k1_partfun1(A_15,B_16,C_17,D_18,E_19,F_20) = k5_relat_1(E_19,F_20)
      | ~ m1_subset_1(F_20,k1_zfmisc_1(k2_zfmisc_1(C_17,D_18)))
      | ~ v1_funct_1(F_20)
      | ~ m1_subset_1(E_19,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_1(E_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1061,plain,(
    ! [A_15,B_16,E_19] :
      ( k1_partfun1(A_15,B_16,'#skF_5','#skF_4',E_19,k2_funct_1('#skF_6')) = k5_relat_1(E_19,k2_funct_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ m1_subset_1(E_19,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_1(E_19) ) ),
    inference(resolution,[status(thm)],[c_1016,c_26])).

tff(c_1183,plain,(
    ! [A_193,B_194,E_195] :
      ( k1_partfun1(A_193,B_194,'#skF_5','#skF_4',E_195,k2_funct_1('#skF_6')) = k5_relat_1(E_195,k2_funct_1('#skF_6'))
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ v1_funct_1(E_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_1061])).

tff(c_1198,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',k2_funct_1('#skF_6')) = k5_relat_1('#skF_6',k2_funct_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_1183])).

tff(c_1210,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',k2_funct_1('#skF_6')) = k5_relat_1('#skF_6',k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1198])).

tff(c_70,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_954,plain,(
    ! [F_185] :
      ( r2_relset_1('#skF_5','#skF_4','#skF_7',F_185)
      | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',F_185))
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(F_185,'#skF_5','#skF_4')
      | ~ v1_funct_1(F_185)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | k1_xboole_0 = '#skF_4'
      | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_942])).

tff(c_972,plain,(
    ! [F_185] :
      ( r2_relset_1('#skF_5','#skF_4','#skF_7',F_185)
      | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',F_185))
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(F_185,'#skF_5','#skF_4')
      | ~ v1_funct_1(F_185)
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_66,c_72,c_70,c_68,c_954])).

tff(c_973,plain,(
    ! [F_185] :
      ( r2_relset_1('#skF_5','#skF_4','#skF_7',F_185)
      | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',F_185))
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(F_185,'#skF_5','#skF_4')
      | ~ v1_funct_1(F_185) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_60,c_972])).

tff(c_1254,plain,
    ( r2_relset_1('#skF_5','#skF_4','#skF_7',k2_funct_1('#skF_6'))
    | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k5_relat_1('#skF_6',k2_funct_1('#skF_6')))
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_973])).

tff(c_1266,plain,
    ( r2_relset_1('#skF_5','#skF_4','#skF_7',k2_funct_1('#skF_6'))
    | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k5_relat_1('#skF_6',k2_funct_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_268,c_1016,c_1254])).

tff(c_1304,plain,(
    ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k5_relat_1('#skF_6',k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1266])).

tff(c_1307,plain,
    ( ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k6_partfun1(k1_relat_1('#skF_6')))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_1304])).

tff(c_1310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_78,c_62,c_404,c_159,c_1307])).

tff(c_1311,plain,(
    r2_relset_1('#skF_5','#skF_4','#skF_7',k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1266])).

tff(c_12,plain,(
    ! [D_11,C_10,A_8,B_9] :
      ( D_11 = C_10
      | ~ r2_relset_1(A_8,B_9,C_10,D_11)
      | ~ m1_subset_1(D_11,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1339,plain,
    ( k2_funct_1('#skF_6') = '#skF_7'
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_1311,c_12])).

tff(c_1342,plain,(
    k2_funct_1('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1016,c_1339])).

tff(c_1344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n013.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 20:37:09 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.63  
% 3.76/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.63  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.76/1.63  
% 3.76/1.63  %Foreground sorts:
% 3.76/1.63  
% 3.76/1.63  
% 3.76/1.63  %Background operators:
% 3.76/1.63  
% 3.76/1.63  
% 3.76/1.63  %Foreground operators:
% 3.76/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.76/1.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.76/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.76/1.63  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.76/1.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.76/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.76/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.76/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.76/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.76/1.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.76/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.76/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.76/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.76/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.76/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.76/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.76/1.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.76/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.76/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.76/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.76/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.76/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.76/1.63  
% 4.13/1.65  tff(f_156, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.13/1.65  tff(f_130, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.13/1.65  tff(f_114, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => ((k2_relset_1(A, B, C) = B) <=> (![D]: (~(D = k1_xboole_0) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, B, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(B, D)))) => (r2_relset_1(A, D, k1_partfun1(A, B, B, D, C, E), k1_partfun1(A, B, B, D, C, F)) => r2_relset_1(B, D, E, F)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_2)).
% 4.13/1.65  tff(f_79, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.13/1.65  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.13/1.65  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.13/1.65  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.13/1.65  tff(f_81, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.13/1.65  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.13/1.65  tff(f_51, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.13/1.65  tff(c_56, plain, (k2_funct_1('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_76, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_62, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_66, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_50, plain, (![C_52, B_51, A_50]: (m1_subset_1(k2_funct_1(C_52), k1_zfmisc_1(k2_zfmisc_1(B_51, A_50))) | k2_relset_1(A_50, B_51, C_52)!=B_51 | ~v2_funct_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_funct_2(C_52, A_50, B_51) | ~v1_funct_1(C_52))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.13/1.65  tff(c_60, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_58, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_213, plain, (![C_83, A_84, B_85]: (v1_funct_1(k2_funct_1(C_83)) | k2_relset_1(A_84, B_85, C_83)!=B_85 | ~v2_funct_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_funct_2(C_83, A_84, B_85) | ~v1_funct_1(C_83))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.13/1.65  tff(c_216, plain, (v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_213])).
% 4.13/1.65  tff(c_222, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_62, c_66, c_216])).
% 4.13/1.65  tff(c_259, plain, (![C_92, B_93, A_94]: (v1_funct_2(k2_funct_1(C_92), B_93, A_94) | k2_relset_1(A_94, B_93, C_92)!=B_93 | ~v2_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))) | ~v1_funct_2(C_92, A_94, B_93) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.13/1.65  tff(c_262, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_259])).
% 4.13/1.65  tff(c_268, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_62, c_66, c_262])).
% 4.13/1.65  tff(c_337, plain, (![C_110, B_111, A_112]: (m1_subset_1(k2_funct_1(C_110), k1_zfmisc_1(k2_zfmisc_1(B_111, A_112))) | k2_relset_1(A_112, B_111, C_110)!=B_111 | ~v2_funct_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))) | ~v1_funct_2(C_110, A_112, B_111) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.13/1.65  tff(c_40, plain, (![A_22, B_23, C_24]: (v1_funct_1('#skF_3'(A_22, B_23, C_24)) | k2_relset_1(A_22, B_23, C_24)=B_23 | k1_xboole_0=B_23 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.13/1.65  tff(c_883, plain, (![B_177, A_178, C_179]: (v1_funct_1('#skF_3'(B_177, A_178, k2_funct_1(C_179))) | k2_relset_1(B_177, A_178, k2_funct_1(C_179))=A_178 | k1_xboole_0=A_178 | ~v1_funct_2(k2_funct_1(C_179), B_177, A_178) | ~v1_funct_1(k2_funct_1(C_179)) | k2_relset_1(A_178, B_177, C_179)!=B_177 | ~v2_funct_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))) | ~v1_funct_2(C_179, A_178, B_177) | ~v1_funct_1(C_179))), inference(resolution, [status(thm)], [c_337, c_40])).
% 4.13/1.65  tff(c_895, plain, (v1_funct_1('#skF_3'('#skF_5', '#skF_4', k2_funct_1('#skF_6'))) | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4' | k1_xboole_0='#skF_4' | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_883])).
% 4.13/1.65  tff(c_904, plain, (v1_funct_1('#skF_3'('#skF_5', '#skF_4', k2_funct_1('#skF_6'))) | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_62, c_66, c_222, c_268, c_895])).
% 4.13/1.65  tff(c_905, plain, (v1_funct_1('#skF_3'('#skF_5', '#skF_4', k2_funct_1('#skF_6'))) | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_60, c_904])).
% 4.13/1.65  tff(c_910, plain, (k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4'), inference(splitLeft, [status(thm)], [c_905])).
% 4.13/1.65  tff(c_292, plain, (![D_99, F_101, A_103, B_100, C_98, E_102]: (k1_partfun1(A_103, B_100, C_98, D_99, E_102, F_101)=k5_relat_1(E_102, F_101) | ~m1_subset_1(F_101, k1_zfmisc_1(k2_zfmisc_1(C_98, D_99))) | ~v1_funct_1(F_101) | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_100))) | ~v1_funct_1(E_102))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.13/1.65  tff(c_294, plain, (![A_103, B_100, E_102]: (k1_partfun1(A_103, B_100, '#skF_4', '#skF_5', E_102, '#skF_6')=k5_relat_1(E_102, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_100))) | ~v1_funct_1(E_102))), inference(resolution, [status(thm)], [c_74, c_292])).
% 4.13/1.65  tff(c_299, plain, (![A_103, B_100, E_102]: (k1_partfun1(A_103, B_100, '#skF_4', '#skF_5', E_102, '#skF_6')=k5_relat_1(E_102, '#skF_6') | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_100))) | ~v1_funct_1(E_102))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_294])).
% 4.13/1.65  tff(c_467, plain, (![B_130, A_131, C_132]: (k1_partfun1(B_130, A_131, '#skF_4', '#skF_5', k2_funct_1(C_132), '#skF_6')=k5_relat_1(k2_funct_1(C_132), '#skF_6') | ~v1_funct_1(k2_funct_1(C_132)) | k2_relset_1(A_131, B_130, C_132)!=B_130 | ~v2_funct_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))) | ~v1_funct_2(C_132, A_131, B_130) | ~v1_funct_1(C_132))), inference(resolution, [status(thm)], [c_337, c_299])).
% 4.13/1.65  tff(c_473, plain, (k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), '#skF_6')=k5_relat_1(k2_funct_1('#skF_6'), '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_467])).
% 4.13/1.65  tff(c_480, plain, (k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), '#skF_6')=k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_62, c_66, c_222, c_473])).
% 4.13/1.65  tff(c_942, plain, (![B_188, F_185, C_184, D_186, A_183, E_187]: (r2_relset_1(B_188, D_186, E_187, F_185) | ~r2_relset_1(A_183, D_186, k1_partfun1(A_183, B_188, B_188, D_186, C_184, E_187), k1_partfun1(A_183, B_188, B_188, D_186, C_184, F_185)) | ~m1_subset_1(F_185, k1_zfmisc_1(k2_zfmisc_1(B_188, D_186))) | ~v1_funct_2(F_185, B_188, D_186) | ~v1_funct_1(F_185) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(B_188, D_186))) | ~v1_funct_2(E_187, B_188, D_186) | ~v1_funct_1(E_187) | k1_xboole_0=D_186 | k2_relset_1(A_183, B_188, C_184)!=B_188 | k1_xboole_0=B_188 | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_188))) | ~v1_funct_2(C_184, A_183, B_188) | ~v1_funct_1(C_184))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.13/1.65  tff(c_948, plain, (![F_185]: (r2_relset_1('#skF_4', '#skF_5', '#skF_6', F_185) | ~r2_relset_1('#skF_5', '#skF_5', k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), F_185)) | ~m1_subset_1(F_185, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2(F_185, '#skF_4', '#skF_5') | ~v1_funct_1(F_185) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | k1_xboole_0='#skF_5' | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))!='#skF_4' | k1_xboole_0='#skF_4' | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_480, c_942])).
% 4.13/1.65  tff(c_966, plain, (![F_185]: (r2_relset_1('#skF_4', '#skF_5', '#skF_6', F_185) | ~r2_relset_1('#skF_5', '#skF_5', k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), F_185)) | ~m1_subset_1(F_185, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2(F_185, '#skF_4', '#skF_5') | ~v1_funct_1(F_185) | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_268, c_910, c_78, c_76, c_74, c_948])).
% 4.13/1.65  tff(c_967, plain, (![F_185]: (r2_relset_1('#skF_4', '#skF_5', '#skF_6', F_185) | ~r2_relset_1('#skF_5', '#skF_5', k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), F_185)) | ~m1_subset_1(F_185, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2(F_185, '#skF_4', '#skF_5') | ~v1_funct_1(F_185) | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_966])).
% 4.13/1.65  tff(c_1007, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_967])).
% 4.13/1.65  tff(c_1010, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_1007])).
% 4.13/1.65  tff(c_1014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_62, c_66, c_1010])).
% 4.13/1.65  tff(c_1016, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_967])).
% 4.13/1.65  tff(c_94, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.13/1.65  tff(c_101, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_94])).
% 4.13/1.65  tff(c_72, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_296, plain, (![A_103, B_100, E_102]: (k1_partfun1(A_103, B_100, '#skF_5', '#skF_4', E_102, '#skF_7')=k5_relat_1(E_102, '#skF_7') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_100))) | ~v1_funct_1(E_102))), inference(resolution, [status(thm)], [c_68, c_292])).
% 4.13/1.65  tff(c_324, plain, (![A_107, B_108, E_109]: (k1_partfun1(A_107, B_108, '#skF_5', '#skF_4', E_109, '#skF_7')=k5_relat_1(E_109, '#skF_7') | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_1(E_109))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_296])).
% 4.13/1.65  tff(c_327, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_324])).
% 4.13/1.65  tff(c_333, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_327])).
% 4.13/1.65  tff(c_64, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k6_partfun1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_404, plain, (r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k6_partfun1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_64])).
% 4.13/1.65  tff(c_110, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.13/1.65  tff(c_117, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_110])).
% 4.13/1.65  tff(c_149, plain, (![B_73, A_74, C_75]: (k1_xboole_0=B_73 | k1_relset_1(A_74, B_73, C_75)=A_74 | ~v1_funct_2(C_75, A_74, B_73) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.13/1.65  tff(c_152, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_149])).
% 4.13/1.65  tff(c_158, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_117, c_152])).
% 4.13/1.65  tff(c_159, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_158])).
% 4.13/1.65  tff(c_28, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.13/1.65  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.13/1.65  tff(c_79, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4])).
% 4.13/1.65  tff(c_26, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (k1_partfun1(A_15, B_16, C_17, D_18, E_19, F_20)=k5_relat_1(E_19, F_20) | ~m1_subset_1(F_20, k1_zfmisc_1(k2_zfmisc_1(C_17, D_18))) | ~v1_funct_1(F_20) | ~m1_subset_1(E_19, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_funct_1(E_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.13/1.65  tff(c_1061, plain, (![A_15, B_16, E_19]: (k1_partfun1(A_15, B_16, '#skF_5', '#skF_4', E_19, k2_funct_1('#skF_6'))=k5_relat_1(E_19, k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~m1_subset_1(E_19, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_funct_1(E_19))), inference(resolution, [status(thm)], [c_1016, c_26])).
% 4.13/1.65  tff(c_1183, plain, (![A_193, B_194, E_195]: (k1_partfun1(A_193, B_194, '#skF_5', '#skF_4', E_195, k2_funct_1('#skF_6'))=k5_relat_1(E_195, k2_funct_1('#skF_6')) | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~v1_funct_1(E_195))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_1061])).
% 4.13/1.65  tff(c_1198, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', k2_funct_1('#skF_6'))=k5_relat_1('#skF_6', k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_1183])).
% 4.13/1.65  tff(c_1210, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', k2_funct_1('#skF_6'))=k5_relat_1('#skF_6', k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1198])).
% 4.13/1.65  tff(c_70, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.13/1.65  tff(c_954, plain, (![F_185]: (r2_relset_1('#skF_5', '#skF_4', '#skF_7', F_185) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', F_185)) | ~m1_subset_1(F_185, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(F_185, '#skF_5', '#skF_4') | ~v1_funct_1(F_185) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | k1_xboole_0='#skF_4' | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_333, c_942])).
% 4.13/1.65  tff(c_972, plain, (![F_185]: (r2_relset_1('#skF_5', '#skF_4', '#skF_7', F_185) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', F_185)) | ~m1_subset_1(F_185, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(F_185, '#skF_5', '#skF_4') | ~v1_funct_1(F_185) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_66, c_72, c_70, c_68, c_954])).
% 4.13/1.65  tff(c_973, plain, (![F_185]: (r2_relset_1('#skF_5', '#skF_4', '#skF_7', F_185) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', F_185)) | ~m1_subset_1(F_185, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(F_185, '#skF_5', '#skF_4') | ~v1_funct_1(F_185))), inference(negUnitSimplification, [status(thm)], [c_58, c_60, c_972])).
% 4.13/1.65  tff(c_1254, plain, (r2_relset_1('#skF_5', '#skF_4', '#skF_7', k2_funct_1('#skF_6')) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k5_relat_1('#skF_6', k2_funct_1('#skF_6'))) | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1210, c_973])).
% 4.13/1.65  tff(c_1266, plain, (r2_relset_1('#skF_5', '#skF_4', '#skF_7', k2_funct_1('#skF_6')) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k5_relat_1('#skF_6', k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_268, c_1016, c_1254])).
% 4.13/1.65  tff(c_1304, plain, (~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k5_relat_1('#skF_6', k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_1266])).
% 4.13/1.65  tff(c_1307, plain, (~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k6_partfun1(k1_relat_1('#skF_6'))) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_79, c_1304])).
% 4.13/1.65  tff(c_1310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_78, c_62, c_404, c_159, c_1307])).
% 4.13/1.65  tff(c_1311, plain, (r2_relset_1('#skF_5', '#skF_4', '#skF_7', k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1266])).
% 4.13/1.65  tff(c_12, plain, (![D_11, C_10, A_8, B_9]: (D_11=C_10 | ~r2_relset_1(A_8, B_9, C_10, D_11) | ~m1_subset_1(D_11, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.13/1.65  tff(c_1339, plain, (k2_funct_1('#skF_6')='#skF_7' | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(resolution, [status(thm)], [c_1311, c_12])).
% 4.13/1.65  tff(c_1342, plain, (k2_funct_1('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1016, c_1339])).
% 4.13/1.65  tff(c_1344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1342])).
% 4.13/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.65  
% 4.13/1.65  Inference rules
% 4.13/1.65  ----------------------
% 4.13/1.65  #Ref     : 0
% 4.13/1.65  #Sup     : 264
% 4.13/1.65  #Fact    : 0
% 4.13/1.65  #Define  : 0
% 4.13/1.65  #Split   : 9
% 4.13/1.65  #Chain   : 0
% 4.13/1.65  #Close   : 0
% 4.13/1.65  
% 4.13/1.65  Ordering : KBO
% 4.13/1.65  
% 4.13/1.65  Simplification rules
% 4.13/1.65  ----------------------
% 4.13/1.65  #Subsume      : 31
% 4.13/1.65  #Demod        : 340
% 4.13/1.65  #Tautology    : 93
% 4.13/1.65  #SimpNegUnit  : 48
% 4.13/1.65  #BackRed      : 5
% 4.13/1.65  
% 4.13/1.65  #Partial instantiations: 0
% 4.13/1.65  #Strategies tried      : 1
% 4.13/1.65  
% 4.13/1.65  Timing (in seconds)
% 4.13/1.65  ----------------------
% 4.13/1.66  Preprocessing        : 0.36
% 4.13/1.66  Parsing              : 0.17
% 4.13/1.66  CNF conversion       : 0.03
% 4.13/1.66  Main loop            : 0.59
% 4.13/1.66  Inferencing          : 0.20
% 4.13/1.66  Reduction            : 0.18
% 4.13/1.66  Demodulation         : 0.13
% 4.13/1.66  BG Simplification    : 0.03
% 4.13/1.66  Subsumption          : 0.13
% 4.13/1.66  Abstraction          : 0.03
% 4.13/1.66  MUC search           : 0.00
% 4.13/1.66  Cooper               : 0.00
% 4.13/1.66  Total                : 0.99
% 4.13/1.66  Index Insertion      : 0.00
% 4.13/1.66  Index Deletion       : 0.00
% 4.13/1.66  Index Matching       : 0.00
% 4.13/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
