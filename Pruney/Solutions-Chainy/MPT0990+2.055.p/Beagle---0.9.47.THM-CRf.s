%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:03 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 274 expanded)
%              Number of leaves         :   38 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  233 (1111 expanded)
%              Number of equality atoms :   98 ( 410 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

tff(f_158,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_116,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_132,axiom,(
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

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_46,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_133,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_146,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_133])).

tff(c_204,plain,(
    ! [B_62,A_63,C_64] :
      ( k1_xboole_0 = B_62
      | k1_relset_1(A_63,B_62,C_64) = A_63
      | ~ v1_funct_2(C_64,A_63,B_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_213,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_204])).

tff(c_222,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_146,c_213])).

tff(c_223,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_222])).

tff(c_107,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_119,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_107])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_118,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_107])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_52,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_145,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_133])).

tff(c_210,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_204])).

tff(c_218,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_145,c_210])).

tff(c_219,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_218])).

tff(c_40,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

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

tff(c_880,plain,(
    ! [A_162,B_163] :
      ( k2_funct_1(A_162) = B_163
      | k6_partfun1(k1_relat_1(A_162)) != k5_relat_1(A_162,B_163)
      | k2_relat_1(A_162) != k1_relat_1(B_163)
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(B_163)
      | ~ v1_relat_1(B_163)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10])).

tff(c_884,plain,(
    ! [B_163] :
      ( k2_funct_1('#skF_3') = B_163
      | k5_relat_1('#skF_3',B_163) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_163)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_163)
      | ~ v1_relat_1(B_163)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_880])).

tff(c_899,plain,(
    ! [B_164] :
      ( k2_funct_1('#skF_3') = B_164
      | k5_relat_1('#skF_3',B_164) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_164)
      | ~ v1_funct_1(B_164)
      | ~ v1_relat_1(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_68,c_52,c_884])).

tff(c_905,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_119,c_899])).

tff(c_913,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_223,c_905])).

tff(c_914,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_913])).

tff(c_918,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_914])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1021,plain,(
    ! [B_190,C_191,A_192] :
      ( k6_partfun1(B_190) = k5_relat_1(k2_funct_1(C_191),C_191)
      | k1_xboole_0 = B_190
      | ~ v2_funct_1(C_191)
      | k2_relset_1(A_192,B_190,C_191) != B_190
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_190)))
      | ~ v1_funct_2(C_191,A_192,B_190)
      | ~ v1_funct_1(C_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1025,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1021])).

tff(c_1031,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_56,c_52,c_1025])).

tff(c_1032,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1031])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_partfun1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6])).

tff(c_1040,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_72])).

tff(c_1047,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_68,c_52,c_1040])).

tff(c_1082,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1047,c_73])).

tff(c_1096,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_1082])).

tff(c_1098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_918,c_1096])).

tff(c_1099,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_914])).

tff(c_628,plain,(
    ! [D_130,A_132,B_131,C_134,E_135,F_133] :
      ( k1_partfun1(A_132,B_131,C_134,D_130,E_135,F_133) = k5_relat_1(E_135,F_133)
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(C_134,D_130)))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131)))
      | ~ v1_funct_1(E_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_634,plain,(
    ! [A_132,B_131,E_135] :
      ( k1_partfun1(A_132,B_131,'#skF_2','#skF_1',E_135,'#skF_4') = k5_relat_1(E_135,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131)))
      | ~ v1_funct_1(E_135) ) ),
    inference(resolution,[status(thm)],[c_58,c_628])).

tff(c_670,plain,(
    ! [A_140,B_141,E_142] :
      ( k1_partfun1(A_140,B_141,'#skF_2','#skF_1',E_142,'#skF_4') = k5_relat_1(E_142,'#skF_4')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_634])).

tff(c_676,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_670])).

tff(c_683,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_676])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1(k6_relat_1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_69,plain,(
    ! [A_16] : m1_subset_1(k6_partfun1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_20])).

tff(c_54,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_264,plain,(
    ! [D_69,C_70,A_71,B_72] :
      ( D_69 = C_70
      | ~ r2_relset_1(A_71,B_72,C_70,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_272,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_264])).

tff(c_287,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_272])).

tff(c_288,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_688,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_288])).

tff(c_787,plain,(
    ! [D_158,A_160,E_159,C_156,B_157,F_161] :
      ( m1_subset_1(k1_partfun1(A_160,B_157,C_156,D_158,E_159,F_161),k1_zfmisc_1(k2_zfmisc_1(A_160,D_158)))
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(C_156,D_158)))
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_157)))
      | ~ v1_funct_1(E_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_841,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_787])).

tff(c_868,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_841])).

tff(c_870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_688,c_868])).

tff(c_871,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_1185,plain,(
    ! [D_209,B_210,C_213,F_212,A_211,E_214] :
      ( k1_partfun1(A_211,B_210,C_213,D_209,E_214,F_212) = k5_relat_1(E_214,F_212)
      | ~ m1_subset_1(F_212,k1_zfmisc_1(k2_zfmisc_1(C_213,D_209)))
      | ~ v1_funct_1(F_212)
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210)))
      | ~ v1_funct_1(E_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1191,plain,(
    ! [A_211,B_210,E_214] :
      ( k1_partfun1(A_211,B_210,'#skF_2','#skF_1',E_214,'#skF_4') = k5_relat_1(E_214,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210)))
      | ~ v1_funct_1(E_214) ) ),
    inference(resolution,[status(thm)],[c_58,c_1185])).

tff(c_1269,plain,(
    ! [A_222,B_223,E_224] :
      ( k1_partfun1(A_222,B_223,'#skF_2','#skF_1',E_224,'#skF_4') = k5_relat_1(E_224,'#skF_4')
      | ~ m1_subset_1(E_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ v1_funct_1(E_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1191])).

tff(c_1275,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1269])).

tff(c_1282,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_871,c_1275])).

tff(c_1284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1099,c_1282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.64  
% 3.91/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.65  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.91/1.65  
% 3.91/1.65  %Foreground sorts:
% 3.91/1.65  
% 3.91/1.65  
% 3.91/1.65  %Background operators:
% 3.91/1.65  
% 3.91/1.65  
% 3.91/1.65  %Foreground operators:
% 3.91/1.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.91/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.91/1.65  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.91/1.65  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.65  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.91/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.91/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.91/1.65  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.91/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.91/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.91/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.91/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.65  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.91/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.91/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.91/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.65  
% 3.91/1.67  tff(f_158, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 3.91/1.67  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.91/1.67  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.91/1.67  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.91/1.67  tff(f_116, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.91/1.67  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 3.91/1.67  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.91/1.67  tff(f_132, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 3.91/1.67  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 3.91/1.67  tff(f_114, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.91/1.67  tff(f_74, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.91/1.67  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.91/1.67  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.91/1.67  tff(c_46, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_50, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_133, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.91/1.67  tff(c_146, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_133])).
% 3.91/1.67  tff(c_204, plain, (![B_62, A_63, C_64]: (k1_xboole_0=B_62 | k1_relset_1(A_63, B_62, C_64)=A_63 | ~v1_funct_2(C_64, A_63, B_62) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.91/1.67  tff(c_213, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_204])).
% 3.91/1.67  tff(c_222, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_146, c_213])).
% 3.91/1.67  tff(c_223, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_222])).
% 3.91/1.67  tff(c_107, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.91/1.67  tff(c_119, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_107])).
% 3.91/1.67  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_118, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_107])).
% 3.91/1.67  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_52, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_145, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_133])).
% 3.91/1.67  tff(c_210, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_204])).
% 3.91/1.67  tff(c_218, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_145, c_210])).
% 3.91/1.67  tff(c_219, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_48, c_218])).
% 3.91/1.67  tff(c_40, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.91/1.67  tff(c_10, plain, (![A_3, B_5]: (k2_funct_1(A_3)=B_5 | k6_relat_1(k1_relat_1(A_3))!=k5_relat_1(A_3, B_5) | k2_relat_1(A_3)!=k1_relat_1(B_5) | ~v2_funct_1(A_3) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.91/1.67  tff(c_880, plain, (![A_162, B_163]: (k2_funct_1(A_162)=B_163 | k6_partfun1(k1_relat_1(A_162))!=k5_relat_1(A_162, B_163) | k2_relat_1(A_162)!=k1_relat_1(B_163) | ~v2_funct_1(A_162) | ~v1_funct_1(B_163) | ~v1_relat_1(B_163) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10])).
% 3.91/1.67  tff(c_884, plain, (![B_163]: (k2_funct_1('#skF_3')=B_163 | k5_relat_1('#skF_3', B_163)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_163) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_163) | ~v1_relat_1(B_163) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_219, c_880])).
% 3.91/1.67  tff(c_899, plain, (![B_164]: (k2_funct_1('#skF_3')=B_164 | k5_relat_1('#skF_3', B_164)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_164) | ~v1_funct_1(B_164) | ~v1_relat_1(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_68, c_52, c_884])).
% 3.91/1.67  tff(c_905, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_119, c_899])).
% 3.91/1.67  tff(c_913, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_223, c_905])).
% 3.91/1.67  tff(c_914, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_913])).
% 3.91/1.67  tff(c_918, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_914])).
% 3.91/1.67  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.91/1.67  tff(c_73, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4])).
% 3.91/1.67  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_1021, plain, (![B_190, C_191, A_192]: (k6_partfun1(B_190)=k5_relat_1(k2_funct_1(C_191), C_191) | k1_xboole_0=B_190 | ~v2_funct_1(C_191) | k2_relset_1(A_192, B_190, C_191)!=B_190 | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_190))) | ~v1_funct_2(C_191, A_192, B_190) | ~v1_funct_1(C_191))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.91/1.67  tff(c_1025, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1021])).
% 3.91/1.67  tff(c_1031, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_56, c_52, c_1025])).
% 3.91/1.67  tff(c_1032, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_1031])).
% 3.91/1.67  tff(c_6, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.91/1.67  tff(c_72, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_partfun1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6])).
% 3.91/1.67  tff(c_1040, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1032, c_72])).
% 3.91/1.67  tff(c_1047, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_68, c_52, c_1040])).
% 3.91/1.67  tff(c_1082, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1047, c_73])).
% 3.91/1.67  tff(c_1096, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_1082])).
% 3.91/1.67  tff(c_1098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_918, c_1096])).
% 3.91/1.67  tff(c_1099, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_914])).
% 3.91/1.67  tff(c_628, plain, (![D_130, A_132, B_131, C_134, E_135, F_133]: (k1_partfun1(A_132, B_131, C_134, D_130, E_135, F_133)=k5_relat_1(E_135, F_133) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(C_134, D_130))) | ~v1_funct_1(F_133) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))) | ~v1_funct_1(E_135))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.67  tff(c_634, plain, (![A_132, B_131, E_135]: (k1_partfun1(A_132, B_131, '#skF_2', '#skF_1', E_135, '#skF_4')=k5_relat_1(E_135, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))) | ~v1_funct_1(E_135))), inference(resolution, [status(thm)], [c_58, c_628])).
% 3.91/1.67  tff(c_670, plain, (![A_140, B_141, E_142]: (k1_partfun1(A_140, B_141, '#skF_2', '#skF_1', E_142, '#skF_4')=k5_relat_1(E_142, '#skF_4') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_1(E_142))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_634])).
% 3.91/1.67  tff(c_676, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_670])).
% 3.91/1.67  tff(c_683, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_676])).
% 3.91/1.67  tff(c_20, plain, (![A_16]: (m1_subset_1(k6_relat_1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.91/1.67  tff(c_69, plain, (![A_16]: (m1_subset_1(k6_partfun1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_20])).
% 3.91/1.67  tff(c_54, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.67  tff(c_264, plain, (![D_69, C_70, A_71, B_72]: (D_69=C_70 | ~r2_relset_1(A_71, B_72, C_70, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.91/1.67  tff(c_272, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_54, c_264])).
% 3.91/1.67  tff(c_287, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_272])).
% 3.91/1.67  tff(c_288, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_287])).
% 3.91/1.67  tff(c_688, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_288])).
% 3.91/1.67  tff(c_787, plain, (![D_158, A_160, E_159, C_156, B_157, F_161]: (m1_subset_1(k1_partfun1(A_160, B_157, C_156, D_158, E_159, F_161), k1_zfmisc_1(k2_zfmisc_1(A_160, D_158))) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(C_156, D_158))) | ~v1_funct_1(F_161) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_157))) | ~v1_funct_1(E_159))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.91/1.67  tff(c_841, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_683, c_787])).
% 3.91/1.67  tff(c_868, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_841])).
% 3.91/1.67  tff(c_870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_688, c_868])).
% 3.91/1.67  tff(c_871, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_287])).
% 3.91/1.67  tff(c_1185, plain, (![D_209, B_210, C_213, F_212, A_211, E_214]: (k1_partfun1(A_211, B_210, C_213, D_209, E_214, F_212)=k5_relat_1(E_214, F_212) | ~m1_subset_1(F_212, k1_zfmisc_1(k2_zfmisc_1(C_213, D_209))) | ~v1_funct_1(F_212) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))) | ~v1_funct_1(E_214))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.67  tff(c_1191, plain, (![A_211, B_210, E_214]: (k1_partfun1(A_211, B_210, '#skF_2', '#skF_1', E_214, '#skF_4')=k5_relat_1(E_214, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))) | ~v1_funct_1(E_214))), inference(resolution, [status(thm)], [c_58, c_1185])).
% 3.91/1.67  tff(c_1269, plain, (![A_222, B_223, E_224]: (k1_partfun1(A_222, B_223, '#skF_2', '#skF_1', E_224, '#skF_4')=k5_relat_1(E_224, '#skF_4') | ~m1_subset_1(E_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))) | ~v1_funct_1(E_224))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1191])).
% 3.91/1.67  tff(c_1275, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1269])).
% 3.91/1.67  tff(c_1282, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_871, c_1275])).
% 3.91/1.67  tff(c_1284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1099, c_1282])).
% 3.91/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.67  
% 3.91/1.67  Inference rules
% 3.91/1.67  ----------------------
% 3.91/1.67  #Ref     : 0
% 3.91/1.67  #Sup     : 267
% 3.91/1.67  #Fact    : 0
% 3.91/1.67  #Define  : 0
% 3.91/1.67  #Split   : 10
% 3.91/1.67  #Chain   : 0
% 3.91/1.67  #Close   : 0
% 3.91/1.67  
% 3.91/1.67  Ordering : KBO
% 3.91/1.67  
% 3.91/1.67  Simplification rules
% 3.91/1.67  ----------------------
% 3.91/1.67  #Subsume      : 13
% 3.91/1.67  #Demod        : 242
% 3.91/1.67  #Tautology    : 88
% 3.91/1.67  #SimpNegUnit  : 23
% 3.91/1.67  #BackRed      : 17
% 3.91/1.67  
% 3.91/1.67  #Partial instantiations: 0
% 3.91/1.67  #Strategies tried      : 1
% 3.91/1.67  
% 3.91/1.67  Timing (in seconds)
% 3.91/1.67  ----------------------
% 3.91/1.67  Preprocessing        : 0.37
% 3.91/1.67  Parsing              : 0.20
% 3.91/1.67  CNF conversion       : 0.02
% 3.91/1.67  Main loop            : 0.53
% 3.91/1.67  Inferencing          : 0.19
% 3.91/1.67  Reduction            : 0.18
% 3.91/1.67  Demodulation         : 0.13
% 3.91/1.67  BG Simplification    : 0.03
% 3.91/1.67  Subsumption          : 0.10
% 3.91/1.67  Abstraction          : 0.03
% 3.91/1.67  MUC search           : 0.00
% 3.91/1.67  Cooper               : 0.00
% 3.91/1.67  Total                : 0.94
% 3.91/1.67  Index Insertion      : 0.00
% 3.91/1.67  Index Deletion       : 0.00
% 3.91/1.67  Index Matching       : 0.00
% 3.91/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
