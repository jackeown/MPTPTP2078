%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:02 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 701 expanded)
%              Number of leaves         :   40 ( 267 expanded)
%              Depth                    :   18
%              Number of atoms          :  302 (3013 expanded)
%              Number of equality atoms :  111 (1131 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_137,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_73,axiom,(
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

tff(f_95,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_135,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_95,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_107,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_95])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_108,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_95])).

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

tff(c_152,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_164,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_152])).

tff(c_223,plain,(
    ! [B_73,A_74,C_75] :
      ( k1_xboole_0 = B_73
      | k1_relset_1(A_74,B_73,C_75) = A_74
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_232,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_223])).

tff(c_241,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_164,c_232])).

tff(c_242,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_241])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_120,plain,(
    ! [A_56,B_57,C_58] :
      ( k2_relset_1(A_56,B_57,C_58) = k2_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_129,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_120])).

tff(c_133,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_129])).

tff(c_46,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_14,plain,(
    ! [A_6,B_8] :
      ( k2_funct_1(A_6) = B_8
      | k6_relat_1(k2_relat_1(A_6)) != k5_relat_1(B_8,A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_525,plain,(
    ! [A_124,B_125] :
      ( k2_funct_1(A_124) = B_125
      | k6_partfun1(k2_relat_1(A_124)) != k5_relat_1(B_125,A_124)
      | k2_relat_1(B_125) != k1_relat_1(A_124)
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_531,plain,(
    ! [B_125] :
      ( k2_funct_1('#skF_3') = B_125
      | k5_relat_1(B_125,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_125) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_525])).

tff(c_536,plain,(
    ! [B_126] :
      ( k2_funct_1('#skF_3') = B_126
      | k5_relat_1(B_126,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_126) != '#skF_1'
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_72,c_56,c_242,c_531])).

tff(c_542,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_536])).

tff(c_551,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_542])).

tff(c_552,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_551])).

tff(c_554,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_552])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_26,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_73,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_26])).

tff(c_109,plain,(
    ! [A_52,B_53,D_54] :
      ( r2_relset_1(A_52,B_53,D_54,D_54)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_116,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_73,c_109])).

tff(c_131,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_120])).

tff(c_458,plain,(
    ! [B_119,C_122,A_120,F_121,E_123,D_118] :
      ( m1_subset_1(k1_partfun1(A_120,B_119,C_122,D_118,E_123,F_121),k1_zfmisc_1(k2_zfmisc_1(A_120,D_118)))
      | ~ m1_subset_1(F_121,k1_zfmisc_1(k2_zfmisc_1(C_122,D_118)))
      | ~ v1_funct_1(F_121)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_1(E_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_313,plain,(
    ! [D_85,C_86,A_87,B_88] :
      ( D_85 = C_86
      | ~ r2_relset_1(A_87,B_88,C_86,D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_321,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_313])).

tff(c_336,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_321])).

tff(c_339,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_474,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_458,c_339])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_474])).

tff(c_516,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_933,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k2_relset_1(A_158,B_159,C_160) = B_159
      | ~ r2_relset_1(B_159,B_159,k1_partfun1(B_159,A_158,A_158,B_159,D_161,C_160),k6_partfun1(B_159))
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_159,A_158)))
      | ~ v1_funct_2(D_161,B_159,A_158)
      | ~ v1_funct_1(D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_2(C_160,A_158,B_159)
      | ~ v1_funct_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_939,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_933])).

tff(c_943,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_116,c_131,c_939])).

tff(c_945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_554,c_943])).

tff(c_946,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_163,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_152])).

tff(c_229,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_223])).

tff(c_237,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_163,c_229])).

tff(c_238,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_237])).

tff(c_947,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_74,plain,(
    ! [A_6,B_8] :
      ( k2_funct_1(A_6) = B_8
      | k6_partfun1(k2_relat_1(A_6)) != k5_relat_1(B_8,A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_951,plain,(
    ! [B_8] :
      ( k2_funct_1('#skF_4') = B_8
      | k5_relat_1(B_8,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_8) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_74])).

tff(c_955,plain,(
    ! [B_8] :
      ( k2_funct_1('#skF_4') = B_8
      | k5_relat_1(B_8,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_8) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_66,c_238,c_951])).

tff(c_963,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_955])).

tff(c_4,plain,(
    ! [A_1] : v2_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_1] : v2_funct_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4])).

tff(c_978,plain,(
    ! [E_169,C_172,D_174,F_171,A_173,B_170] :
      ( k1_partfun1(A_173,B_170,C_172,D_174,E_169,F_171) = k5_relat_1(E_169,F_171)
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(C_172,D_174)))
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_173,B_170)))
      | ~ v1_funct_1(E_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_982,plain,(
    ! [A_173,B_170,E_169] :
      ( k1_partfun1(A_173,B_170,'#skF_2','#skF_1',E_169,'#skF_4') = k5_relat_1(E_169,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_173,B_170)))
      | ~ v1_funct_1(E_169) ) ),
    inference(resolution,[status(thm)],[c_62,c_978])).

tff(c_1091,plain,(
    ! [A_189,B_190,E_191] :
      ( k1_partfun1(A_189,B_190,'#skF_2','#skF_1',E_191,'#skF_4') = k5_relat_1(E_191,'#skF_4')
      | ~ m1_subset_1(E_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ v1_funct_1(E_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_982])).

tff(c_1103,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1091])).

tff(c_1111,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_516,c_1103])).

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

tff(c_1115,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_6])).

tff(c_1122,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_66,c_108,c_72,c_77,c_133,c_238,c_1115])).

tff(c_1124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_963,c_1122])).

tff(c_1126,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_1127,plain,(
    ! [B_192] :
      ( k2_funct_1('#skF_4') = B_192
      | k5_relat_1(B_192,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_192) != '#skF_2'
      | ~ v1_funct_1(B_192)
      | ~ v1_relat_1(B_192) ) ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_1130,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_1127])).

tff(c_1139,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_133,c_1130])).

tff(c_1144,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1139])).

tff(c_1160,plain,(
    ! [D_205,C_203,F_202,E_200,A_204,B_201] :
      ( k1_partfun1(A_204,B_201,C_203,D_205,E_200,F_202) = k5_relat_1(E_200,F_202)
      | ~ m1_subset_1(F_202,k1_zfmisc_1(k2_zfmisc_1(C_203,D_205)))
      | ~ v1_funct_1(F_202)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_204,B_201)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1164,plain,(
    ! [A_204,B_201,E_200] :
      ( k1_partfun1(A_204,B_201,'#skF_2','#skF_1',E_200,'#skF_4') = k5_relat_1(E_200,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_204,B_201)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_62,c_1160])).

tff(c_1278,plain,(
    ! [A_220,B_221,E_222] :
      ( k1_partfun1(A_220,B_221,'#skF_2','#skF_1',E_222,'#skF_4') = k5_relat_1(E_222,'#skF_4')
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221)))
      | ~ v1_funct_1(E_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1164])).

tff(c_1290,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1278])).

tff(c_1298,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_516,c_1290])).

tff(c_1300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1144,c_1298])).

tff(c_1301,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1139])).

tff(c_12,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k2_funct_1(A_5)) = k6_relat_1(k1_relat_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_75,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k2_funct_1(A_5)) = k6_partfun1(k1_relat_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_1313,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1301,c_75])).

tff(c_1324,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_66,c_1126,c_238,c_1313])).

tff(c_1326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_946,c_1324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.80  
% 4.20/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.81  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.20/1.81  
% 4.20/1.81  %Foreground sorts:
% 4.20/1.81  
% 4.20/1.81  
% 4.20/1.81  %Background operators:
% 4.20/1.81  
% 4.20/1.81  
% 4.20/1.81  %Foreground operators:
% 4.20/1.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.20/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.20/1.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.20/1.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.20/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.81  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.20/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.20/1.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.20/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.20/1.81  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.20/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.20/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.20/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.20/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.20/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/1.81  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.20/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.20/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.20/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.20/1.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.20/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.20/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.81  
% 4.35/1.83  tff(f_180, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.35/1.83  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.35/1.83  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.35/1.83  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.35/1.83  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.35/1.83  tff(f_137, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.35/1.83  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 4.35/1.83  tff(f_95, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.35/1.83  tff(f_93, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.35/1.83  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.35/1.83  tff(f_154, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.35/1.83  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.35/1.83  tff(f_135, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.35/1.83  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 4.35/1.83  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.35/1.83  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_95, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.35/1.83  tff(c_107, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_95])).
% 4.35/1.83  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_108, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_95])).
% 4.35/1.83  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_152, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.35/1.83  tff(c_164, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_152])).
% 4.35/1.83  tff(c_223, plain, (![B_73, A_74, C_75]: (k1_xboole_0=B_73 | k1_relset_1(A_74, B_73, C_75)=A_74 | ~v1_funct_2(C_75, A_74, B_73) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.35/1.83  tff(c_232, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_223])).
% 4.35/1.83  tff(c_241, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_164, c_232])).
% 4.35/1.83  tff(c_242, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_241])).
% 4.35/1.83  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_120, plain, (![A_56, B_57, C_58]: (k2_relset_1(A_56, B_57, C_58)=k2_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.35/1.83  tff(c_129, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_120])).
% 4.35/1.83  tff(c_133, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_129])).
% 4.35/1.83  tff(c_46, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.35/1.83  tff(c_14, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_relat_1(k2_relat_1(A_6))!=k5_relat_1(B_8, A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.35/1.83  tff(c_525, plain, (![A_124, B_125]: (k2_funct_1(A_124)=B_125 | k6_partfun1(k2_relat_1(A_124))!=k5_relat_1(B_125, A_124) | k2_relat_1(B_125)!=k1_relat_1(A_124) | ~v2_funct_1(A_124) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 4.35/1.83  tff(c_531, plain, (![B_125]: (k2_funct_1('#skF_3')=B_125 | k5_relat_1(B_125, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_125)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_125) | ~v1_relat_1(B_125) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_525])).
% 4.35/1.83  tff(c_536, plain, (![B_126]: (k2_funct_1('#skF_3')=B_126 | k5_relat_1(B_126, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_126)!='#skF_1' | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_72, c_56, c_242, c_531])).
% 4.35/1.83  tff(c_542, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_107, c_536])).
% 4.35/1.83  tff(c_551, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_542])).
% 4.35/1.83  tff(c_552, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_551])).
% 4.35/1.83  tff(c_554, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_552])).
% 4.35/1.83  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_26, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.35/1.83  tff(c_73, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_26])).
% 4.35/1.83  tff(c_109, plain, (![A_52, B_53, D_54]: (r2_relset_1(A_52, B_53, D_54, D_54) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.35/1.83  tff(c_116, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_73, c_109])).
% 4.35/1.83  tff(c_131, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_120])).
% 4.35/1.83  tff(c_458, plain, (![B_119, C_122, A_120, F_121, E_123, D_118]: (m1_subset_1(k1_partfun1(A_120, B_119, C_122, D_118, E_123, F_121), k1_zfmisc_1(k2_zfmisc_1(A_120, D_118))) | ~m1_subset_1(F_121, k1_zfmisc_1(k2_zfmisc_1(C_122, D_118))) | ~v1_funct_1(F_121) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_1(E_123))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.35/1.83  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_313, plain, (![D_85, C_86, A_87, B_88]: (D_85=C_86 | ~r2_relset_1(A_87, B_88, C_86, D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.35/1.83  tff(c_321, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_313])).
% 4.35/1.83  tff(c_336, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_321])).
% 4.35/1.83  tff(c_339, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_336])).
% 4.35/1.83  tff(c_474, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_458, c_339])).
% 4.35/1.83  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_474])).
% 4.35/1.83  tff(c_516, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_336])).
% 4.35/1.83  tff(c_933, plain, (![A_158, B_159, C_160, D_161]: (k2_relset_1(A_158, B_159, C_160)=B_159 | ~r2_relset_1(B_159, B_159, k1_partfun1(B_159, A_158, A_158, B_159, D_161, C_160), k6_partfun1(B_159)) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_159, A_158))) | ~v1_funct_2(D_161, B_159, A_158) | ~v1_funct_1(D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_2(C_160, A_158, B_159) | ~v1_funct_1(C_160))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.35/1.83  tff(c_939, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_516, c_933])).
% 4.35/1.83  tff(c_943, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_116, c_131, c_939])).
% 4.35/1.83  tff(c_945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_554, c_943])).
% 4.35/1.83  tff(c_946, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_552])).
% 4.35/1.83  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.35/1.83  tff(c_163, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_152])).
% 4.35/1.83  tff(c_229, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_223])).
% 4.35/1.83  tff(c_237, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_163, c_229])).
% 4.35/1.83  tff(c_238, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_237])).
% 4.35/1.83  tff(c_947, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_552])).
% 4.35/1.83  tff(c_74, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_partfun1(k2_relat_1(A_6))!=k5_relat_1(B_8, A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 4.35/1.83  tff(c_951, plain, (![B_8]: (k2_funct_1('#skF_4')=B_8 | k5_relat_1(B_8, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_8)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_947, c_74])).
% 4.35/1.83  tff(c_955, plain, (![B_8]: (k2_funct_1('#skF_4')=B_8 | k5_relat_1(B_8, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_8)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_8) | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_66, c_238, c_951])).
% 4.35/1.83  tff(c_963, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_955])).
% 4.35/1.83  tff(c_4, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.35/1.83  tff(c_77, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4])).
% 4.35/1.83  tff(c_978, plain, (![E_169, C_172, D_174, F_171, A_173, B_170]: (k1_partfun1(A_173, B_170, C_172, D_174, E_169, F_171)=k5_relat_1(E_169, F_171) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(C_172, D_174))) | ~v1_funct_1(F_171) | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(A_173, B_170))) | ~v1_funct_1(E_169))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.35/1.83  tff(c_982, plain, (![A_173, B_170, E_169]: (k1_partfun1(A_173, B_170, '#skF_2', '#skF_1', E_169, '#skF_4')=k5_relat_1(E_169, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(A_173, B_170))) | ~v1_funct_1(E_169))), inference(resolution, [status(thm)], [c_62, c_978])).
% 4.35/1.83  tff(c_1091, plain, (![A_189, B_190, E_191]: (k1_partfun1(A_189, B_190, '#skF_2', '#skF_1', E_191, '#skF_4')=k5_relat_1(E_191, '#skF_4') | ~m1_subset_1(E_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~v1_funct_1(E_191))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_982])).
% 4.35/1.83  tff(c_1103, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1091])).
% 4.35/1.83  tff(c_1111, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_516, c_1103])).
% 4.35/1.83  tff(c_6, plain, (![A_2, B_4]: (v2_funct_1(A_2) | k2_relat_1(B_4)!=k1_relat_1(A_2) | ~v2_funct_1(k5_relat_1(B_4, A_2)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.35/1.83  tff(c_1115, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1111, c_6])).
% 4.35/1.83  tff(c_1122, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_66, c_108, c_72, c_77, c_133, c_238, c_1115])).
% 4.35/1.83  tff(c_1124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_963, c_1122])).
% 4.35/1.83  tff(c_1126, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_955])).
% 4.35/1.83  tff(c_1127, plain, (![B_192]: (k2_funct_1('#skF_4')=B_192 | k5_relat_1(B_192, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_192)!='#skF_2' | ~v1_funct_1(B_192) | ~v1_relat_1(B_192))), inference(splitRight, [status(thm)], [c_955])).
% 4.35/1.83  tff(c_1130, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_1127])).
% 4.35/1.83  tff(c_1139, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_133, c_1130])).
% 4.35/1.83  tff(c_1144, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1139])).
% 4.35/1.83  tff(c_1160, plain, (![D_205, C_203, F_202, E_200, A_204, B_201]: (k1_partfun1(A_204, B_201, C_203, D_205, E_200, F_202)=k5_relat_1(E_200, F_202) | ~m1_subset_1(F_202, k1_zfmisc_1(k2_zfmisc_1(C_203, D_205))) | ~v1_funct_1(F_202) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_204, B_201))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.35/1.83  tff(c_1164, plain, (![A_204, B_201, E_200]: (k1_partfun1(A_204, B_201, '#skF_2', '#skF_1', E_200, '#skF_4')=k5_relat_1(E_200, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_204, B_201))) | ~v1_funct_1(E_200))), inference(resolution, [status(thm)], [c_62, c_1160])).
% 4.35/1.83  tff(c_1278, plain, (![A_220, B_221, E_222]: (k1_partfun1(A_220, B_221, '#skF_2', '#skF_1', E_222, '#skF_4')=k5_relat_1(E_222, '#skF_4') | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))) | ~v1_funct_1(E_222))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1164])).
% 4.35/1.83  tff(c_1290, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1278])).
% 4.35/1.83  tff(c_1298, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_516, c_1290])).
% 4.35/1.83  tff(c_1300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1144, c_1298])).
% 4.35/1.83  tff(c_1301, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1139])).
% 4.35/1.83  tff(c_12, plain, (![A_5]: (k5_relat_1(A_5, k2_funct_1(A_5))=k6_relat_1(k1_relat_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.35/1.83  tff(c_75, plain, (![A_5]: (k5_relat_1(A_5, k2_funct_1(A_5))=k6_partfun1(k1_relat_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 4.35/1.83  tff(c_1313, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1301, c_75])).
% 4.35/1.83  tff(c_1324, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_66, c_1126, c_238, c_1313])).
% 4.35/1.83  tff(c_1326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_946, c_1324])).
% 4.35/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.83  
% 4.35/1.83  Inference rules
% 4.35/1.83  ----------------------
% 4.35/1.83  #Ref     : 0
% 4.35/1.83  #Sup     : 268
% 4.35/1.83  #Fact    : 0
% 4.35/1.83  #Define  : 0
% 4.35/1.83  #Split   : 14
% 4.35/1.83  #Chain   : 0
% 4.35/1.83  #Close   : 0
% 4.35/1.83  
% 4.35/1.83  Ordering : KBO
% 4.35/1.83  
% 4.35/1.83  Simplification rules
% 4.35/1.83  ----------------------
% 4.35/1.83  #Subsume      : 2
% 4.35/1.83  #Demod        : 204
% 4.35/1.83  #Tautology    : 66
% 4.35/1.83  #SimpNegUnit  : 17
% 4.35/1.83  #BackRed      : 8
% 4.35/1.83  
% 4.35/1.83  #Partial instantiations: 0
% 4.35/1.83  #Strategies tried      : 1
% 4.35/1.83  
% 4.35/1.83  Timing (in seconds)
% 4.35/1.83  ----------------------
% 4.44/1.83  Preprocessing        : 0.41
% 4.44/1.83  Parsing              : 0.21
% 4.44/1.83  CNF conversion       : 0.03
% 4.44/1.83  Main loop            : 0.59
% 4.44/1.83  Inferencing          : 0.20
% 4.44/1.83  Reduction            : 0.20
% 4.44/1.83  Demodulation         : 0.14
% 4.44/1.83  BG Simplification    : 0.03
% 4.44/1.83  Subsumption          : 0.10
% 4.44/1.83  Abstraction          : 0.03
% 4.44/1.83  MUC search           : 0.00
% 4.44/1.83  Cooper               : 0.00
% 4.44/1.83  Total                : 1.05
% 4.44/1.84  Index Insertion      : 0.00
% 4.44/1.84  Index Deletion       : 0.00
% 4.44/1.84  Index Matching       : 0.00
% 4.44/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
