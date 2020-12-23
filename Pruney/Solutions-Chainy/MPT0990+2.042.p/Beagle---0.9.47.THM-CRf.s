%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:01 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 617 expanded)
%              Number of leaves         :   41 ( 238 expanded)
%              Depth                    :   18
%              Number of atoms          :  295 (2687 expanded)
%              Number of equality atoms :  108 ( 992 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_135,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_123,axiom,(
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

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_44,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_133,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_42,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_89,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_101,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_89])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_131,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_143,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_131])).

tff(c_216,plain,(
    ! [B_73,A_74,C_75] :
      ( k1_xboole_0 = B_73
      | k1_relset_1(A_74,B_73,C_75) = A_74
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_225,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_216])).

tff(c_234,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_143,c_225])).

tff(c_235,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_234])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_100,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_89])).

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

tff(c_142,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_131])).

tff(c_222,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_216])).

tff(c_230,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_142,c_222])).

tff(c_231,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_230])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_162,plain,(
    ! [A_63,B_64,C_65] :
      ( k2_relset_1(A_63,B_64,C_65) = k2_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_168,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_162])).

tff(c_174,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_168])).

tff(c_44,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_relat_1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_498,plain,(
    ! [A_122,B_123] :
      ( k2_funct_1(A_122) = B_123
      | k6_partfun1(k2_relat_1(A_122)) != k5_relat_1(B_123,A_122)
      | k2_relat_1(B_123) != k1_relat_1(A_122)
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_500,plain,(
    ! [B_123] :
      ( k2_funct_1('#skF_3') = B_123
      | k5_relat_1(B_123,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_123) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_498])).

tff(c_503,plain,(
    ! [B_124] :
      ( k2_funct_1('#skF_3') = B_124
      | k5_relat_1(B_124,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_124) != '#skF_1'
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_70,c_54,c_231,c_500])).

tff(c_509,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_101,c_503])).

tff(c_516,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_509])).

tff(c_517,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_516])).

tff(c_521,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_40,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_120,plain,(
    ! [A_54,B_55,D_56] :
      ( r2_relset_1(A_54,B_55,D_56,D_56)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_127,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_40,c_120])).

tff(c_175,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_162])).

tff(c_428,plain,(
    ! [E_121,D_116,A_117,B_120,F_119,C_118] :
      ( m1_subset_1(k1_partfun1(A_117,B_120,C_118,D_116,E_121,F_119),k1_zfmisc_1(k2_zfmisc_1(A_117,D_116)))
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_118,D_116)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_117,B_120)))
      | ~ v1_funct_1(E_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_286,plain,(
    ! [D_85,C_86,A_87,B_88] :
      ( D_85 = C_86
      | ~ r2_relset_1(A_87,B_88,C_86,D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_294,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_286])).

tff(c_309,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_294])).

tff(c_310,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_444,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_428,c_310])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_444])).

tff(c_489,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_847,plain,(
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

tff(c_850,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_847])).

tff(c_852,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_127,c_175,c_850])).

tff(c_854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_521,c_852])).

tff(c_856,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_71,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_partfun1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_860,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_71])).

tff(c_864,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_64,c_235,c_860])).

tff(c_872,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_864])).

tff(c_6,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    ! [A_4] : v2_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_887,plain,(
    ! [C_170,D_172,A_171,E_167,B_168,F_169] :
      ( k1_partfun1(A_171,B_168,C_170,D_172,E_167,F_169) = k5_relat_1(E_167,F_169)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(C_170,D_172)))
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_171,B_168)))
      | ~ v1_funct_1(E_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_893,plain,(
    ! [A_171,B_168,E_167] :
      ( k1_partfun1(A_171,B_168,'#skF_2','#skF_1',E_167,'#skF_4') = k5_relat_1(E_167,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_171,B_168)))
      | ~ v1_funct_1(E_167) ) ),
    inference(resolution,[status(thm)],[c_60,c_887])).

tff(c_1000,plain,(
    ! [A_187,B_188,E_189] :
      ( k1_partfun1(A_187,B_188,'#skF_2','#skF_1',E_189,'#skF_4') = k5_relat_1(E_189,'#skF_4')
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(E_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_893])).

tff(c_1009,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1000])).

tff(c_1017,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_489,c_1009])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( v2_funct_1(A_1)
      | k2_relat_1(B_3) != k1_relat_1(A_1)
      | ~ v2_funct_1(k5_relat_1(B_3,A_1))
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1027,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_2])).

tff(c_1033,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_64,c_100,c_70,c_72,c_174,c_235,c_1027])).

tff(c_1035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_872,c_1033])).

tff(c_1037,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_864])).

tff(c_1038,plain,(
    ! [B_190] :
      ( k2_funct_1('#skF_4') = B_190
      | k5_relat_1(B_190,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_190) != '#skF_2'
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190) ) ),
    inference(splitRight,[status(thm)],[c_864])).

tff(c_1047,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_1038])).

tff(c_1054,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_174,c_1047])).

tff(c_1055,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1054])).

tff(c_1071,plain,(
    ! [A_202,B_199,E_198,D_203,C_201,F_200] :
      ( k1_partfun1(A_202,B_199,C_201,D_203,E_198,F_200) = k5_relat_1(E_198,F_200)
      | ~ m1_subset_1(F_200,k1_zfmisc_1(k2_zfmisc_1(C_201,D_203)))
      | ~ v1_funct_1(F_200)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_202,B_199)))
      | ~ v1_funct_1(E_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1077,plain,(
    ! [A_202,B_199,E_198] :
      ( k1_partfun1(A_202,B_199,'#skF_2','#skF_1',E_198,'#skF_4') = k5_relat_1(E_198,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_202,B_199)))
      | ~ v1_funct_1(E_198) ) ),
    inference(resolution,[status(thm)],[c_60,c_1071])).

tff(c_1392,plain,(
    ! [A_225,B_226,E_227] :
      ( k1_partfun1(A_225,B_226,'#skF_2','#skF_1',E_227,'#skF_4') = k5_relat_1(E_227,'#skF_4')
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226)))
      | ~ v1_funct_1(E_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1077])).

tff(c_1407,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1392])).

tff(c_1421,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_489,c_1407])).

tff(c_1423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1055,c_1421])).

tff(c_1424,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_10,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1430,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1424,c_10])).

tff(c_1434,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_64,c_1037,c_1430])).

tff(c_1436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:03:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.63  
% 3.83/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.63  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.83/1.63  
% 3.83/1.63  %Foreground sorts:
% 3.83/1.63  
% 3.83/1.63  
% 3.83/1.63  %Background operators:
% 3.83/1.63  
% 3.83/1.63  
% 3.83/1.63  %Foreground operators:
% 3.83/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.83/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.83/1.63  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.83/1.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.83/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.83/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.83/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.83/1.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.83/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.83/1.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.83/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.83/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.83/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.83/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.83/1.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.83/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.83/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.83/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.83/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.83/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.83/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.83/1.63  
% 3.83/1.66  tff(f_178, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 3.83/1.66  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.83/1.66  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.83/1.66  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.83/1.66  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.83/1.66  tff(f_135, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.83/1.66  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 3.83/1.66  tff(f_123, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.83/1.66  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.83/1.66  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.83/1.66  tff(f_152, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 3.83/1.66  tff(f_44, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 3.83/1.66  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.83/1.66  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 3.83/1.66  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.83/1.66  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_89, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.83/1.66  tff(c_101, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_89])).
% 3.83/1.66  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_131, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.83/1.66  tff(c_143, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_131])).
% 3.83/1.66  tff(c_216, plain, (![B_73, A_74, C_75]: (k1_xboole_0=B_73 | k1_relset_1(A_74, B_73, C_75)=A_74 | ~v1_funct_2(C_75, A_74, B_73) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.83/1.66  tff(c_225, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_216])).
% 3.83/1.66  tff(c_234, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_143, c_225])).
% 3.83/1.66  tff(c_235, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_234])).
% 3.83/1.66  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_100, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_89])).
% 3.83/1.66  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_142, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_131])).
% 3.83/1.66  tff(c_222, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_216])).
% 3.83/1.66  tff(c_230, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_142, c_222])).
% 3.83/1.66  tff(c_231, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_230])).
% 3.83/1.66  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_162, plain, (![A_63, B_64, C_65]: (k2_relset_1(A_63, B_64, C_65)=k2_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.83/1.66  tff(c_168, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_162])).
% 3.83/1.66  tff(c_174, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_168])).
% 3.83/1.66  tff(c_44, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.83/1.66  tff(c_8, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.83/1.66  tff(c_498, plain, (![A_122, B_123]: (k2_funct_1(A_122)=B_123 | k6_partfun1(k2_relat_1(A_122))!=k5_relat_1(B_123, A_122) | k2_relat_1(B_123)!=k1_relat_1(A_122) | ~v2_funct_1(A_122) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 3.83/1.66  tff(c_500, plain, (![B_123]: (k2_funct_1('#skF_3')=B_123 | k5_relat_1(B_123, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_123)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_123) | ~v1_relat_1(B_123) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_174, c_498])).
% 3.83/1.66  tff(c_503, plain, (![B_124]: (k2_funct_1('#skF_3')=B_124 | k5_relat_1(B_124, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_124)!='#skF_1' | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_70, c_54, c_231, c_500])).
% 3.83/1.66  tff(c_509, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_101, c_503])).
% 3.83/1.66  tff(c_516, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_509])).
% 3.83/1.66  tff(c_517, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_48, c_516])).
% 3.83/1.66  tff(c_521, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_517])).
% 3.83/1.66  tff(c_40, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.83/1.66  tff(c_120, plain, (![A_54, B_55, D_56]: (r2_relset_1(A_54, B_55, D_56, D_56) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.83/1.66  tff(c_127, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_40, c_120])).
% 3.83/1.66  tff(c_175, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_162])).
% 3.83/1.66  tff(c_428, plain, (![E_121, D_116, A_117, B_120, F_119, C_118]: (m1_subset_1(k1_partfun1(A_117, B_120, C_118, D_116, E_121, F_119), k1_zfmisc_1(k2_zfmisc_1(A_117, D_116))) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_118, D_116))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_117, B_120))) | ~v1_funct_1(E_121))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.83/1.66  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.83/1.66  tff(c_286, plain, (![D_85, C_86, A_87, B_88]: (D_85=C_86 | ~r2_relset_1(A_87, B_88, C_86, D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.83/1.66  tff(c_294, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_286])).
% 3.83/1.66  tff(c_309, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_294])).
% 3.83/1.66  tff(c_310, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_309])).
% 3.83/1.66  tff(c_444, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_428, c_310])).
% 3.83/1.66  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_444])).
% 3.83/1.66  tff(c_489, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_309])).
% 3.83/1.66  tff(c_847, plain, (![A_156, B_157, C_158, D_159]: (k2_relset_1(A_156, B_157, C_158)=B_157 | ~r2_relset_1(B_157, B_157, k1_partfun1(B_157, A_156, A_156, B_157, D_159, C_158), k6_partfun1(B_157)) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(B_157, A_156))) | ~v1_funct_2(D_159, B_157, A_156) | ~v1_funct_1(D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_2(C_158, A_156, B_157) | ~v1_funct_1(C_158))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.83/1.66  tff(c_850, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_489, c_847])).
% 3.83/1.66  tff(c_852, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_127, c_175, c_850])).
% 3.83/1.66  tff(c_854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_521, c_852])).
% 3.83/1.66  tff(c_856, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_517])).
% 3.83/1.66  tff(c_71, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_partfun1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 3.83/1.66  tff(c_860, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_856, c_71])).
% 3.83/1.66  tff(c_864, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_64, c_235, c_860])).
% 3.83/1.66  tff(c_872, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_864])).
% 3.83/1.66  tff(c_6, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.83/1.66  tff(c_72, plain, (![A_4]: (v2_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 3.83/1.66  tff(c_887, plain, (![C_170, D_172, A_171, E_167, B_168, F_169]: (k1_partfun1(A_171, B_168, C_170, D_172, E_167, F_169)=k5_relat_1(E_167, F_169) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(C_170, D_172))) | ~v1_funct_1(F_169) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_171, B_168))) | ~v1_funct_1(E_167))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.83/1.66  tff(c_893, plain, (![A_171, B_168, E_167]: (k1_partfun1(A_171, B_168, '#skF_2', '#skF_1', E_167, '#skF_4')=k5_relat_1(E_167, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_171, B_168))) | ~v1_funct_1(E_167))), inference(resolution, [status(thm)], [c_60, c_887])).
% 3.83/1.66  tff(c_1000, plain, (![A_187, B_188, E_189]: (k1_partfun1(A_187, B_188, '#skF_2', '#skF_1', E_189, '#skF_4')=k5_relat_1(E_189, '#skF_4') | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1(E_189))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_893])).
% 3.83/1.66  tff(c_1009, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1000])).
% 3.83/1.66  tff(c_1017, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_489, c_1009])).
% 3.83/1.66  tff(c_2, plain, (![A_1, B_3]: (v2_funct_1(A_1) | k2_relat_1(B_3)!=k1_relat_1(A_1) | ~v2_funct_1(k5_relat_1(B_3, A_1)) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.83/1.66  tff(c_1027, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1017, c_2])).
% 3.83/1.66  tff(c_1033, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_64, c_100, c_70, c_72, c_174, c_235, c_1027])).
% 3.83/1.66  tff(c_1035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_872, c_1033])).
% 3.83/1.66  tff(c_1037, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_864])).
% 3.83/1.66  tff(c_1038, plain, (![B_190]: (k2_funct_1('#skF_4')=B_190 | k5_relat_1(B_190, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_190)!='#skF_2' | ~v1_funct_1(B_190) | ~v1_relat_1(B_190))), inference(splitRight, [status(thm)], [c_864])).
% 3.83/1.66  tff(c_1047, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_1038])).
% 3.83/1.66  tff(c_1054, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_174, c_1047])).
% 3.83/1.66  tff(c_1055, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1054])).
% 3.83/1.66  tff(c_1071, plain, (![A_202, B_199, E_198, D_203, C_201, F_200]: (k1_partfun1(A_202, B_199, C_201, D_203, E_198, F_200)=k5_relat_1(E_198, F_200) | ~m1_subset_1(F_200, k1_zfmisc_1(k2_zfmisc_1(C_201, D_203))) | ~v1_funct_1(F_200) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_202, B_199))) | ~v1_funct_1(E_198))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.83/1.66  tff(c_1077, plain, (![A_202, B_199, E_198]: (k1_partfun1(A_202, B_199, '#skF_2', '#skF_1', E_198, '#skF_4')=k5_relat_1(E_198, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_202, B_199))) | ~v1_funct_1(E_198))), inference(resolution, [status(thm)], [c_60, c_1071])).
% 3.83/1.66  tff(c_1392, plain, (![A_225, B_226, E_227]: (k1_partfun1(A_225, B_226, '#skF_2', '#skF_1', E_227, '#skF_4')=k5_relat_1(E_227, '#skF_4') | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))) | ~v1_funct_1(E_227))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1077])).
% 3.83/1.66  tff(c_1407, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1392])).
% 3.83/1.66  tff(c_1421, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_489, c_1407])).
% 3.83/1.66  tff(c_1423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1055, c_1421])).
% 3.83/1.66  tff(c_1424, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1054])).
% 3.83/1.66  tff(c_10, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.83/1.66  tff(c_1430, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1424, c_10])).
% 3.83/1.66  tff(c_1434, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_64, c_1037, c_1430])).
% 3.83/1.66  tff(c_1436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1434])).
% 3.83/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.66  
% 3.83/1.66  Inference rules
% 3.83/1.66  ----------------------
% 3.83/1.66  #Ref     : 0
% 3.83/1.66  #Sup     : 294
% 3.83/1.66  #Fact    : 0
% 3.83/1.66  #Define  : 0
% 3.83/1.66  #Split   : 15
% 3.83/1.66  #Chain   : 0
% 3.83/1.66  #Close   : 0
% 3.83/1.66  
% 3.83/1.66  Ordering : KBO
% 3.83/1.66  
% 3.83/1.66  Simplification rules
% 3.83/1.66  ----------------------
% 3.83/1.66  #Subsume      : 2
% 3.83/1.66  #Demod        : 223
% 3.83/1.66  #Tautology    : 73
% 3.83/1.66  #SimpNegUnit  : 19
% 3.83/1.66  #BackRed      : 10
% 3.83/1.66  
% 3.83/1.66  #Partial instantiations: 0
% 3.83/1.66  #Strategies tried      : 1
% 3.83/1.66  
% 3.83/1.66  Timing (in seconds)
% 3.83/1.66  ----------------------
% 3.83/1.66  Preprocessing        : 0.35
% 3.83/1.66  Parsing              : 0.19
% 3.83/1.66  CNF conversion       : 0.02
% 3.83/1.66  Main loop            : 0.52
% 3.83/1.66  Inferencing          : 0.19
% 3.83/1.66  Reduction            : 0.17
% 3.83/1.66  Demodulation         : 0.12
% 3.83/1.66  BG Simplification    : 0.03
% 3.83/1.66  Subsumption          : 0.09
% 3.83/1.66  Abstraction          : 0.03
% 3.83/1.66  MUC search           : 0.00
% 3.83/1.66  Cooper               : 0.00
% 3.83/1.66  Total                : 0.92
% 3.83/1.66  Index Insertion      : 0.00
% 3.83/1.66  Index Deletion       : 0.00
% 3.83/1.66  Index Matching       : 0.00
% 3.83/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
