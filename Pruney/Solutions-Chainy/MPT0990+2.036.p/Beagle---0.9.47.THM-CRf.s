%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:00 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 617 expanded)
%              Number of leaves         :   41 ( 238 expanded)
%              Depth                    :   18
%              Number of atoms          :  296 (2688 expanded)
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

tff(f_180,negated_conjecture,(
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
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_137,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_154,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_135,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_93,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_106,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_93])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_135,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_147,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_135])).

tff(c_220,plain,(
    ! [B_73,A_74,C_75] :
      ( k1_xboole_0 = B_73
      | k1_relset_1(A_74,B_73,C_75) = A_74
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_229,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_220])).

tff(c_238,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_147,c_229])).

tff(c_239,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_238])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_105,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_93])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_146,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_135])).

tff(c_226,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_220])).

tff(c_234,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_146,c_226])).

tff(c_235,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_234])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_166,plain,(
    ! [A_63,B_64,C_65] :
      ( k2_relset_1(A_63,B_64,C_65) = k2_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_172,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_166])).

tff(c_178,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_172])).

tff(c_46,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

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

tff(c_502,plain,(
    ! [A_122,B_123] :
      ( k2_funct_1(A_122) = B_123
      | k6_partfun1(k2_relat_1(A_122)) != k5_relat_1(B_123,A_122)
      | k2_relat_1(B_123) != k1_relat_1(A_122)
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_504,plain,(
    ! [B_123] :
      ( k2_funct_1('#skF_3') = B_123
      | k5_relat_1(B_123,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_123) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_502])).

tff(c_507,plain,(
    ! [B_124] :
      ( k2_funct_1('#skF_3') = B_124
      | k5_relat_1(B_124,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_124) != '#skF_1'
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_72,c_56,c_235,c_504])).

tff(c_510,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_507])).

tff(c_519,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_510])).

tff(c_520,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_519])).

tff(c_525,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_42,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_124,plain,(
    ! [A_54,B_55,D_56] :
      ( r2_relset_1(A_54,B_55,D_56,D_56)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_131,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_42,c_124])).

tff(c_179,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_166])).

tff(c_432,plain,(
    ! [E_121,D_116,A_117,B_120,F_119,C_118] :
      ( m1_subset_1(k1_partfun1(A_117,B_120,C_118,D_116,E_121,F_119),k1_zfmisc_1(k2_zfmisc_1(A_117,D_116)))
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_118,D_116)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_117,B_120)))
      | ~ v1_funct_1(E_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_290,plain,(
    ! [D_85,C_86,A_87,B_88] :
      ( D_85 = C_86
      | ~ r2_relset_1(A_87,B_88,C_86,D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_298,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_290])).

tff(c_313,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_298])).

tff(c_314,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_448,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_432,c_314])).

tff(c_492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_448])).

tff(c_493,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_851,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k2_relset_1(A_156,B_157,C_158) = B_157
      | ~ r2_relset_1(B_157,B_157,k1_partfun1(B_157,A_156,A_156,B_157,D_159,C_158),k6_partfun1(B_157))
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(B_157,A_156)))
      | ~ v1_funct_2(D_159,B_157,A_156)
      | ~ v1_funct_1(D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_funct_2(C_158,A_156,B_157)
      | ~ v1_funct_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_854,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_851])).

tff(c_856,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_131,c_179,c_854])).

tff(c_858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_856])).

tff(c_860,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_73,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_partfun1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_864,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_73])).

tff(c_868,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_66,c_239,c_864])).

tff(c_876,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_868])).

tff(c_4,plain,(
    ! [A_1] : v2_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [A_1] : v2_funct_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4])).

tff(c_891,plain,(
    ! [C_170,D_172,A_171,E_167,B_168,F_169] :
      ( k1_partfun1(A_171,B_168,C_170,D_172,E_167,F_169) = k5_relat_1(E_167,F_169)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(C_170,D_172)))
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_171,B_168)))
      | ~ v1_funct_1(E_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_897,plain,(
    ! [A_171,B_168,E_167] :
      ( k1_partfun1(A_171,B_168,'#skF_2','#skF_1',E_167,'#skF_4') = k5_relat_1(E_167,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_171,B_168)))
      | ~ v1_funct_1(E_167) ) ),
    inference(resolution,[status(thm)],[c_62,c_891])).

tff(c_1004,plain,(
    ! [A_187,B_188,E_189] :
      ( k1_partfun1(A_187,B_188,'#skF_2','#skF_1',E_189,'#skF_4') = k5_relat_1(E_189,'#skF_4')
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(E_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_897])).

tff(c_1013,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1004])).

tff(c_1021,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_493,c_1013])).

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
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_6])).

tff(c_1035,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_66,c_105,c_72,c_74,c_178,c_239,c_1028])).

tff(c_1037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_876,c_1035])).

tff(c_1039,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_868])).

tff(c_1040,plain,(
    ! [B_190] :
      ( k2_funct_1('#skF_4') = B_190
      | k5_relat_1(B_190,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_190) != '#skF_2'
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190) ) ),
    inference(splitRight,[status(thm)],[c_868])).

tff(c_1046,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_1040])).

tff(c_1055,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_178,c_1046])).

tff(c_1057,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1055])).

tff(c_1073,plain,(
    ! [A_202,B_199,E_198,D_203,C_201,F_200] :
      ( k1_partfun1(A_202,B_199,C_201,D_203,E_198,F_200) = k5_relat_1(E_198,F_200)
      | ~ m1_subset_1(F_200,k1_zfmisc_1(k2_zfmisc_1(C_201,D_203)))
      | ~ v1_funct_1(F_200)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_202,B_199)))
      | ~ v1_funct_1(E_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1079,plain,(
    ! [A_202,B_199,E_198] :
      ( k1_partfun1(A_202,B_199,'#skF_2','#skF_1',E_198,'#skF_4') = k5_relat_1(E_198,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_202,B_199)))
      | ~ v1_funct_1(E_198) ) ),
    inference(resolution,[status(thm)],[c_62,c_1073])).

tff(c_1394,plain,(
    ! [A_225,B_226,E_227] :
      ( k1_partfun1(A_225,B_226,'#skF_2','#skF_1',E_227,'#skF_4') = k5_relat_1(E_227,'#skF_4')
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226)))
      | ~ v1_funct_1(E_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1079])).

tff(c_1409,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1394])).

tff(c_1423,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_493,c_1409])).

tff(c_1425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1057,c_1423])).

tff(c_1426,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1055])).

tff(c_12,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1432,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1426,c_12])).

tff(c_1436,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_66,c_1039,c_1432])).

tff(c_1438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:35:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.73  
% 3.97/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.73  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.97/1.73  
% 3.97/1.73  %Foreground sorts:
% 3.97/1.73  
% 3.97/1.73  
% 3.97/1.73  %Background operators:
% 3.97/1.73  
% 3.97/1.73  
% 3.97/1.73  %Foreground operators:
% 3.97/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.97/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.97/1.73  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.97/1.73  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.97/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.73  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.97/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.97/1.73  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.97/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.97/1.73  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.97/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.97/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.97/1.73  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.97/1.74  tff('#skF_3', type, '#skF_3': $i).
% 3.97/1.74  tff('#skF_1', type, '#skF_1': $i).
% 3.97/1.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.97/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.97/1.74  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.97/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.97/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.97/1.74  tff('#skF_4', type, '#skF_4': $i).
% 3.97/1.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.97/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.97/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.97/1.74  
% 3.97/1.76  tff(f_180, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 3.97/1.76  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.97/1.76  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.97/1.76  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.97/1.76  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.97/1.76  tff(f_137, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.97/1.76  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 3.97/1.76  tff(f_125, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.97/1.76  tff(f_91, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.97/1.76  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.97/1.76  tff(f_154, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 3.97/1.76  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.97/1.76  tff(f_135, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.97/1.76  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 3.97/1.76  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.97/1.76  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_93, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.97/1.76  tff(c_106, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_93])).
% 3.97/1.76  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_135, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.97/1.76  tff(c_147, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_135])).
% 3.97/1.76  tff(c_220, plain, (![B_73, A_74, C_75]: (k1_xboole_0=B_73 | k1_relset_1(A_74, B_73, C_75)=A_74 | ~v1_funct_2(C_75, A_74, B_73) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.97/1.76  tff(c_229, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_220])).
% 3.97/1.76  tff(c_238, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_147, c_229])).
% 3.97/1.76  tff(c_239, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_238])).
% 3.97/1.76  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_105, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_93])).
% 3.97/1.76  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_146, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_135])).
% 3.97/1.76  tff(c_226, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_220])).
% 3.97/1.76  tff(c_234, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_146, c_226])).
% 3.97/1.76  tff(c_235, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_234])).
% 3.97/1.76  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_166, plain, (![A_63, B_64, C_65]: (k2_relset_1(A_63, B_64, C_65)=k2_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.97/1.76  tff(c_172, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_166])).
% 3.97/1.76  tff(c_178, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_172])).
% 3.97/1.76  tff(c_46, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.97/1.76  tff(c_10, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.97/1.76  tff(c_502, plain, (![A_122, B_123]: (k2_funct_1(A_122)=B_123 | k6_partfun1(k2_relat_1(A_122))!=k5_relat_1(B_123, A_122) | k2_relat_1(B_123)!=k1_relat_1(A_122) | ~v2_funct_1(A_122) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 3.97/1.76  tff(c_504, plain, (![B_123]: (k2_funct_1('#skF_3')=B_123 | k5_relat_1(B_123, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_123)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_123) | ~v1_relat_1(B_123) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_502])).
% 3.97/1.76  tff(c_507, plain, (![B_124]: (k2_funct_1('#skF_3')=B_124 | k5_relat_1(B_124, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_124)!='#skF_1' | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_72, c_56, c_235, c_504])).
% 3.97/1.76  tff(c_510, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_507])).
% 3.97/1.76  tff(c_519, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_510])).
% 3.97/1.76  tff(c_520, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_519])).
% 3.97/1.76  tff(c_525, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_520])).
% 3.97/1.76  tff(c_42, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.97/1.76  tff(c_124, plain, (![A_54, B_55, D_56]: (r2_relset_1(A_54, B_55, D_56, D_56) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.97/1.76  tff(c_131, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_42, c_124])).
% 3.97/1.76  tff(c_179, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_166])).
% 3.97/1.76  tff(c_432, plain, (![E_121, D_116, A_117, B_120, F_119, C_118]: (m1_subset_1(k1_partfun1(A_117, B_120, C_118, D_116, E_121, F_119), k1_zfmisc_1(k2_zfmisc_1(A_117, D_116))) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_118, D_116))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_117, B_120))) | ~v1_funct_1(E_121))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.97/1.76  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.97/1.76  tff(c_290, plain, (![D_85, C_86, A_87, B_88]: (D_85=C_86 | ~r2_relset_1(A_87, B_88, C_86, D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.97/1.76  tff(c_298, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_290])).
% 3.97/1.76  tff(c_313, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_298])).
% 3.97/1.76  tff(c_314, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_313])).
% 3.97/1.76  tff(c_448, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_432, c_314])).
% 3.97/1.76  tff(c_492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_448])).
% 3.97/1.76  tff(c_493, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_313])).
% 3.97/1.76  tff(c_851, plain, (![A_156, B_157, C_158, D_159]: (k2_relset_1(A_156, B_157, C_158)=B_157 | ~r2_relset_1(B_157, B_157, k1_partfun1(B_157, A_156, A_156, B_157, D_159, C_158), k6_partfun1(B_157)) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(B_157, A_156))) | ~v1_funct_2(D_159, B_157, A_156) | ~v1_funct_1(D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_2(C_158, A_156, B_157) | ~v1_funct_1(C_158))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.97/1.76  tff(c_854, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_493, c_851])).
% 3.97/1.76  tff(c_856, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_131, c_179, c_854])).
% 3.97/1.76  tff(c_858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_525, c_856])).
% 3.97/1.76  tff(c_860, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_520])).
% 3.97/1.76  tff(c_73, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_partfun1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 3.97/1.76  tff(c_864, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_860, c_73])).
% 3.97/1.76  tff(c_868, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_66, c_239, c_864])).
% 3.97/1.76  tff(c_876, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_868])).
% 3.97/1.76  tff(c_4, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.97/1.76  tff(c_74, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4])).
% 3.97/1.76  tff(c_891, plain, (![C_170, D_172, A_171, E_167, B_168, F_169]: (k1_partfun1(A_171, B_168, C_170, D_172, E_167, F_169)=k5_relat_1(E_167, F_169) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(C_170, D_172))) | ~v1_funct_1(F_169) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_171, B_168))) | ~v1_funct_1(E_167))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.97/1.76  tff(c_897, plain, (![A_171, B_168, E_167]: (k1_partfun1(A_171, B_168, '#skF_2', '#skF_1', E_167, '#skF_4')=k5_relat_1(E_167, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_171, B_168))) | ~v1_funct_1(E_167))), inference(resolution, [status(thm)], [c_62, c_891])).
% 3.97/1.76  tff(c_1004, plain, (![A_187, B_188, E_189]: (k1_partfun1(A_187, B_188, '#skF_2', '#skF_1', E_189, '#skF_4')=k5_relat_1(E_189, '#skF_4') | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1(E_189))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_897])).
% 3.97/1.76  tff(c_1013, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1004])).
% 3.97/1.76  tff(c_1021, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_493, c_1013])).
% 3.97/1.76  tff(c_6, plain, (![A_2, B_4]: (v2_funct_1(A_2) | k2_relat_1(B_4)!=k1_relat_1(A_2) | ~v2_funct_1(k5_relat_1(B_4, A_2)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.97/1.76  tff(c_1028, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1021, c_6])).
% 3.97/1.76  tff(c_1035, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_66, c_105, c_72, c_74, c_178, c_239, c_1028])).
% 3.97/1.76  tff(c_1037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_876, c_1035])).
% 3.97/1.76  tff(c_1039, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_868])).
% 3.97/1.76  tff(c_1040, plain, (![B_190]: (k2_funct_1('#skF_4')=B_190 | k5_relat_1(B_190, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_190)!='#skF_2' | ~v1_funct_1(B_190) | ~v1_relat_1(B_190))), inference(splitRight, [status(thm)], [c_868])).
% 3.97/1.76  tff(c_1046, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_105, c_1040])).
% 3.97/1.76  tff(c_1055, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_178, c_1046])).
% 3.97/1.76  tff(c_1057, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1055])).
% 3.97/1.76  tff(c_1073, plain, (![A_202, B_199, E_198, D_203, C_201, F_200]: (k1_partfun1(A_202, B_199, C_201, D_203, E_198, F_200)=k5_relat_1(E_198, F_200) | ~m1_subset_1(F_200, k1_zfmisc_1(k2_zfmisc_1(C_201, D_203))) | ~v1_funct_1(F_200) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_202, B_199))) | ~v1_funct_1(E_198))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.97/1.76  tff(c_1079, plain, (![A_202, B_199, E_198]: (k1_partfun1(A_202, B_199, '#skF_2', '#skF_1', E_198, '#skF_4')=k5_relat_1(E_198, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_202, B_199))) | ~v1_funct_1(E_198))), inference(resolution, [status(thm)], [c_62, c_1073])).
% 3.97/1.76  tff(c_1394, plain, (![A_225, B_226, E_227]: (k1_partfun1(A_225, B_226, '#skF_2', '#skF_1', E_227, '#skF_4')=k5_relat_1(E_227, '#skF_4') | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))) | ~v1_funct_1(E_227))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1079])).
% 3.97/1.76  tff(c_1409, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1394])).
% 3.97/1.76  tff(c_1423, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_493, c_1409])).
% 3.97/1.76  tff(c_1425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1057, c_1423])).
% 3.97/1.76  tff(c_1426, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1055])).
% 3.97/1.76  tff(c_12, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.97/1.76  tff(c_1432, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1426, c_12])).
% 3.97/1.76  tff(c_1436, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_66, c_1039, c_1432])).
% 3.97/1.76  tff(c_1438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1436])).
% 3.97/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.76  
% 3.97/1.76  Inference rules
% 3.97/1.76  ----------------------
% 3.97/1.76  #Ref     : 0
% 3.97/1.76  #Sup     : 294
% 3.97/1.76  #Fact    : 0
% 3.97/1.76  #Define  : 0
% 3.97/1.76  #Split   : 15
% 3.97/1.76  #Chain   : 0
% 3.97/1.76  #Close   : 0
% 3.97/1.76  
% 3.97/1.76  Ordering : KBO
% 3.97/1.76  
% 3.97/1.76  Simplification rules
% 3.97/1.76  ----------------------
% 3.97/1.76  #Subsume      : 2
% 3.97/1.76  #Demod        : 217
% 3.97/1.76  #Tautology    : 73
% 3.97/1.76  #SimpNegUnit  : 19
% 3.97/1.76  #BackRed      : 10
% 3.97/1.76  
% 3.97/1.76  #Partial instantiations: 0
% 3.97/1.76  #Strategies tried      : 1
% 3.97/1.76  
% 3.97/1.76  Timing (in seconds)
% 3.97/1.76  ----------------------
% 3.97/1.76  Preprocessing        : 0.38
% 3.97/1.76  Parsing              : 0.21
% 3.97/1.76  CNF conversion       : 0.02
% 3.97/1.76  Main loop            : 0.54
% 3.97/1.76  Inferencing          : 0.20
% 3.97/1.76  Reduction            : 0.18
% 3.97/1.76  Demodulation         : 0.13
% 3.97/1.76  BG Simplification    : 0.03
% 3.97/1.76  Subsumption          : 0.09
% 3.97/1.76  Abstraction          : 0.03
% 3.97/1.76  MUC search           : 0.00
% 3.97/1.76  Cooper               : 0.00
% 3.97/1.76  Total                : 0.97
% 3.97/1.76  Index Insertion      : 0.00
% 3.97/1.76  Index Deletion       : 0.00
% 3.97/1.76  Index Matching       : 0.00
% 3.97/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
