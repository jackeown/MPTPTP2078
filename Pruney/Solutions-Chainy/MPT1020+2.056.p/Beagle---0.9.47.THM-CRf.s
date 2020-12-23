%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:59 EST 2020

% Result     : Theorem 4.96s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :  189 (2046 expanded)
%              Number of leaves         :   46 ( 686 expanded)
%              Depth                    :   16
%              Number of atoms          :  366 (5072 expanded)
%              Number of equality atoms :  116 (1560 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_204,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_138,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_182,axiom,(
    ! [A,B,C] :
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

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_84,axiom,(
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

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_881,plain,(
    ! [A_133,B_134,D_135] :
      ( r2_relset_1(A_133,B_134,D_135,D_135)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_890,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_881])).

tff(c_50,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_10,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_83,plain,(
    ! [A_7] : k1_relat_1(k6_partfun1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10])).

tff(c_16,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,(
    ! [A_9] : v1_relat_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_115,plain,(
    ! [A_54] :
      ( k1_relat_1(A_54) != k1_xboole_0
      | k1_xboole_0 = A_54
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_121,plain,(
    ! [A_9] :
      ( k1_relat_1(k6_partfun1(A_9)) != k1_xboole_0
      | k6_partfun1(A_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80,c_115])).

tff(c_124,plain,(
    ! [A_9] :
      ( k1_xboole_0 != A_9
      | k6_partfun1(A_9) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_121])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_206,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_60])).

tff(c_262,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_76,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_74,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_70,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_207,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_213,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_207])).

tff(c_222,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_213])).

tff(c_279,plain,(
    ! [C_65,B_66,A_67] :
      ( v5_relat_1(C_65,B_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_290,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_279])).

tff(c_337,plain,(
    ! [B_78,A_79] :
      ( k2_relat_1(B_78) = A_79
      | ~ v2_funct_2(B_78,A_79)
      | ~ v5_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_349,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_290,c_337])).

tff(c_361,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_349])).

tff(c_722,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_72,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_827,plain,(
    ! [C_129,B_130,A_131] :
      ( v2_funct_2(C_129,B_130)
      | ~ v3_funct_2(C_129,A_131,B_130)
      | ~ v1_funct_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_833,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_827])).

tff(c_841,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_833])).

tff(c_843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_722,c_841])).

tff(c_844,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_898,plain,(
    ! [A_137,B_138,C_139] :
      ( k2_relset_1(A_137,B_138,C_139) = k2_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_904,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_898])).

tff(c_911,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_904])).

tff(c_968,plain,(
    ! [C_143,A_144,B_145] :
      ( v2_funct_1(C_143)
      | ~ v3_funct_2(C_143,A_144,B_145)
      | ~ v1_funct_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_974,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_968])).

tff(c_982,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_974])).

tff(c_1480,plain,(
    ! [C_206,D_207,B_208,A_209] :
      ( k2_funct_1(C_206) = D_207
      | k1_xboole_0 = B_208
      | k1_xboole_0 = A_209
      | ~ v2_funct_1(C_206)
      | ~ r2_relset_1(A_209,A_209,k1_partfun1(A_209,B_208,B_208,A_209,C_206,D_207),k6_partfun1(A_209))
      | k2_relset_1(A_209,B_208,C_206) != B_208
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(B_208,A_209)))
      | ~ v1_funct_2(D_207,B_208,A_209)
      | ~ v1_funct_1(D_207)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_209,B_208)))
      | ~ v1_funct_2(C_206,A_209,B_208)
      | ~ v1_funct_1(C_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1483,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1480])).

tff(c_1489,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_66,c_62,c_911,c_982,c_1483])).

tff(c_1490,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_1489])).

tff(c_1193,plain,(
    ! [A_168,B_169] :
      ( k2_funct_2(A_168,B_169) = k2_funct_1(B_169)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(k2_zfmisc_1(A_168,A_168)))
      | ~ v3_funct_2(B_169,A_168,A_168)
      | ~ v1_funct_2(B_169,A_168,A_168)
      | ~ v1_funct_1(B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1202,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1193])).

tff(c_1210,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_1202])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1214,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_58])).

tff(c_1491,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1214])).

tff(c_1495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_1491])).

tff(c_1497,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_232,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_222,c_6])).

tff(c_242,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_1499,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1497,c_242])).

tff(c_1599,plain,(
    ! [C_220,B_221,A_222] :
      ( v5_relat_1(C_220,B_221)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_222,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1610,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_1599])).

tff(c_1663,plain,(
    ! [B_229,A_230] :
      ( k2_relat_1(B_229) = A_230
      | ~ v2_funct_2(B_229,A_230)
      | ~ v5_relat_1(B_229,A_230)
      | ~ v1_relat_1(B_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1675,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1610,c_1663])).

tff(c_1688,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_1675])).

tff(c_1689,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1499,c_1688])).

tff(c_1847,plain,(
    ! [C_248,B_249,A_250] :
      ( v2_funct_2(C_248,B_249)
      | ~ v3_funct_2(C_248,A_250,B_249)
      | ~ v1_funct_1(C_248)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_250,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1856,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1847])).

tff(c_1865,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1856])).

tff(c_1867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1689,c_1865])).

tff(c_1868,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_1888,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1868,c_1868,c_206])).

tff(c_1889,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1888])).

tff(c_1869,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_1883,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1868,c_1869])).

tff(c_1995,plain,(
    ! [C_260,B_261,A_262] :
      ( v5_relat_1(C_260,B_261)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_262,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2006,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_1995])).

tff(c_2039,plain,(
    ! [B_268,A_269] :
      ( k2_relat_1(B_268) = A_269
      | ~ v2_funct_2(B_268,A_269)
      | ~ v5_relat_1(B_268,A_269)
      | ~ v1_relat_1(B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2051,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2006,c_2039])).

tff(c_2063,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_1883,c_2051])).

tff(c_2064,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1889,c_2063])).

tff(c_2256,plain,(
    ! [C_287,B_288,A_289] :
      ( v2_funct_2(C_287,B_288)
      | ~ v3_funct_2(C_287,A_289,B_288)
      | ~ v1_funct_1(C_287)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_289,B_288))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2265,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_2256])).

tff(c_2276,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_2265])).

tff(c_2278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2064,c_2276])).

tff(c_2280,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1888])).

tff(c_2283,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_1868])).

tff(c_175,plain,(
    ! [A_57] : m1_subset_1(k6_partfun1(A_57),k1_zfmisc_1(k2_zfmisc_1(A_57,A_57))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_178,plain,(
    ! [A_9] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_9,A_9)))
      | k1_xboole_0 != A_9 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_175])).

tff(c_2873,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_9,A_9)))
      | A_9 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2283,c_2283,c_178])).

tff(c_2970,plain,(
    ! [A_364,B_365,D_366] :
      ( r2_relset_1(A_364,B_365,D_366,D_366)
      | ~ m1_subset_1(D_366,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2987,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2873,c_2970])).

tff(c_2284,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_222])).

tff(c_2290,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_76])).

tff(c_1876,plain,(
    ! [A_9] :
      ( A_9 != '#skF_2'
      | k6_partfun1(A_9) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1868,c_1868,c_124])).

tff(c_2759,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_2280,c_1876])).

tff(c_126,plain,(
    ! [A_55] :
      ( k1_xboole_0 != A_55
      | k6_partfun1(A_55) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_121])).

tff(c_18,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_79,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_142,plain,(
    ! [A_55] :
      ( v2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_55 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_79])).

tff(c_161,plain,(
    ! [A_55] : k1_xboole_0 != A_55 ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_167,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_161])).

tff(c_168,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_1874,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1868,c_168])).

tff(c_2282,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_1874])).

tff(c_132,plain,(
    ! [A_55] :
      ( k1_relat_1(k1_xboole_0) = A_55
      | k1_xboole_0 != A_55 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_83])).

tff(c_1873,plain,(
    ! [A_55] :
      ( k1_relat_1('#skF_2') = A_55
      | A_55 != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1868,c_1868,c_132])).

tff(c_2793,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_2280,c_1873])).

tff(c_2281,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_2280,c_1883])).

tff(c_14,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k6_relat_1(k2_relat_1(A_8))) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k6_partfun1(k2_relat_1(A_8))) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_22,plain,(
    ! [A_13,B_15] :
      ( k2_funct_1(A_13) = B_15
      | k6_relat_1(k1_relat_1(A_13)) != k5_relat_1(A_13,B_15)
      | k2_relat_1(A_13) != k1_relat_1(B_15)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3292,plain,(
    ! [A_413,B_414] :
      ( k2_funct_1(A_413) = B_414
      | k6_partfun1(k1_relat_1(A_413)) != k5_relat_1(A_413,B_414)
      | k2_relat_1(A_413) != k1_relat_1(B_414)
      | ~ v2_funct_1(A_413)
      | ~ v1_funct_1(B_414)
      | ~ v1_relat_1(B_414)
      | ~ v1_funct_1(A_413)
      | ~ v1_relat_1(A_413) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_22])).

tff(c_3301,plain,(
    ! [A_8] :
      ( k6_partfun1(k2_relat_1(A_8)) = k2_funct_1(A_8)
      | k6_partfun1(k1_relat_1(A_8)) != A_8
      | k1_relat_1(k6_partfun1(k2_relat_1(A_8))) != k2_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(k6_partfun1(k2_relat_1(A_8)))
      | ~ v1_relat_1(k6_partfun1(k2_relat_1(A_8)))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_3292])).

tff(c_3507,plain,(
    ! [A_428] :
      ( k6_partfun1(k2_relat_1(A_428)) = k2_funct_1(A_428)
      | k6_partfun1(k1_relat_1(A_428)) != A_428
      | ~ v2_funct_1(A_428)
      | ~ v1_funct_1(k6_partfun1(k2_relat_1(A_428)))
      | ~ v1_funct_1(A_428)
      | ~ v1_relat_1(A_428) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_83,c_3301])).

tff(c_3516,plain,
    ( k6_partfun1(k2_relat_1('#skF_1')) = k2_funct_1('#skF_1')
    | k6_partfun1(k1_relat_1('#skF_1')) != '#skF_1'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2281,c_3507])).

tff(c_3523,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2284,c_2290,c_2290,c_2759,c_2282,c_2759,c_2793,c_2759,c_2281,c_3516])).

tff(c_2288,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_74])).

tff(c_2289,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_72])).

tff(c_3229,plain,(
    ! [A_401,B_402] :
      ( k2_funct_2(A_401,B_402) = k2_funct_1(B_402)
      | ~ m1_subset_1(B_402,k1_zfmisc_1(k2_zfmisc_1(A_401,A_401)))
      | ~ v3_funct_2(B_402,A_401,A_401)
      | ~ v1_funct_2(B_402,A_401,A_401)
      | ~ v1_funct_1(B_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3232,plain,(
    ! [A_9] :
      ( k2_funct_2(A_9,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_9,A_9)
      | ~ v1_funct_2('#skF_1',A_9,A_9)
      | ~ v1_funct_1('#skF_1')
      | A_9 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_2873,c_3229])).

tff(c_3241,plain,(
    ! [A_403] :
      ( k2_funct_2(A_403,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_403,A_403)
      | ~ v1_funct_2('#skF_1',A_403,A_403)
      | A_403 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2290,c_3232])).

tff(c_3244,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2289,c_3241])).

tff(c_3247,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2288,c_3244])).

tff(c_216,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_207])).

tff(c_225,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_216])).

tff(c_240,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_225,c_6])).

tff(c_2329,plain,
    ( k2_relat_1('#skF_3') != '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2283,c_2283,c_240])).

tff(c_2330,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2329])).

tff(c_2367,plain,(
    ! [C_293,B_294,A_295] :
      ( v5_relat_1(C_293,B_294)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_295,B_294))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2379,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_2367])).

tff(c_2568,plain,(
    ! [B_313,A_314] :
      ( k2_relat_1(B_313) = A_314
      | ~ v2_funct_2(B_313,A_314)
      | ~ v5_relat_1(B_313,A_314)
      | ~ v1_relat_1(B_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2577,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2379,c_2568])).

tff(c_2586,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_2577])).

tff(c_2587,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2330,c_2586])).

tff(c_64,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_2716,plain,(
    ! [C_336,B_337,A_338] :
      ( v2_funct_2(C_336,B_337)
      | ~ v3_funct_2(C_336,A_338,B_337)
      | ~ v1_funct_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_338,B_337))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2725,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2716])).

tff(c_2733,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2725])).

tff(c_2735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2587,c_2733])).

tff(c_2736,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2329])).

tff(c_2286,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_58])).

tff(c_2756,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2736,c_2286])).

tff(c_3248,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3247,c_2756])).

tff(c_3529,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3523,c_3248])).

tff(c_3536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2987,c_3529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.96/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.95  
% 4.96/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.96  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.96/1.96  
% 4.96/1.96  %Foreground sorts:
% 4.96/1.96  
% 4.96/1.96  
% 4.96/1.96  %Background operators:
% 4.96/1.96  
% 4.96/1.96  
% 4.96/1.96  %Foreground operators:
% 4.96/1.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.96/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.96/1.96  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.96/1.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.96/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.96/1.96  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.96/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.96/1.96  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.96/1.96  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.96/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.96/1.96  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.96/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.96/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.96/1.96  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.96/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.96/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.96/1.96  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.96/1.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.96/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.96/1.96  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.96/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.96/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.96/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.96/1.96  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.96/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.96/1.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.96/1.96  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.96/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.96/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.96/1.96  
% 5.44/1.98  tff(f_204, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 5.44/1.98  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.44/1.98  tff(f_138, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.44/1.98  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.44/1.98  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.44/1.98  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.44/1.98  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.44/1.98  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.44/1.98  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.44/1.98  tff(f_122, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.44/1.98  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.44/1.98  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.44/1.98  tff(f_182, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 5.44/1.98  tff(f_136, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.44/1.98  tff(f_126, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.44/1.98  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 5.44/1.98  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 5.44/1.98  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.44/1.98  tff(c_881, plain, (![A_133, B_134, D_135]: (r2_relset_1(A_133, B_134, D_135, D_135) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.44/1.98  tff(c_890, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_881])).
% 5.44/1.98  tff(c_50, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.44/1.98  tff(c_10, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.44/1.98  tff(c_83, plain, (![A_7]: (k1_relat_1(k6_partfun1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_10])).
% 5.44/1.98  tff(c_16, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.44/1.98  tff(c_80, plain, (![A_9]: (v1_relat_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16])).
% 5.44/1.98  tff(c_115, plain, (![A_54]: (k1_relat_1(A_54)!=k1_xboole_0 | k1_xboole_0=A_54 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.44/1.98  tff(c_121, plain, (![A_9]: (k1_relat_1(k6_partfun1(A_9))!=k1_xboole_0 | k6_partfun1(A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_115])).
% 5.44/1.98  tff(c_124, plain, (![A_9]: (k1_xboole_0!=A_9 | k6_partfun1(A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_121])).
% 5.44/1.98  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.44/1.98  tff(c_206, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_124, c_60])).
% 5.44/1.98  tff(c_262, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_206])).
% 5.44/1.98  tff(c_76, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.44/1.98  tff(c_74, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.44/1.98  tff(c_70, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.44/1.98  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.44/1.98  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.44/1.98  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.44/1.98  tff(c_207, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.44/1.98  tff(c_213, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_207])).
% 5.44/1.98  tff(c_222, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_213])).
% 5.44/1.98  tff(c_279, plain, (![C_65, B_66, A_67]: (v5_relat_1(C_65, B_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.44/1.98  tff(c_290, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_279])).
% 5.44/1.98  tff(c_337, plain, (![B_78, A_79]: (k2_relat_1(B_78)=A_79 | ~v2_funct_2(B_78, A_79) | ~v5_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.44/1.98  tff(c_349, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_290, c_337])).
% 5.44/1.98  tff(c_361, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_349])).
% 5.44/1.98  tff(c_722, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_361])).
% 5.44/1.98  tff(c_72, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.44/1.98  tff(c_827, plain, (![C_129, B_130, A_131]: (v2_funct_2(C_129, B_130) | ~v3_funct_2(C_129, A_131, B_130) | ~v1_funct_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.44/1.98  tff(c_833, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_827])).
% 5.44/1.98  tff(c_841, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_833])).
% 5.44/1.98  tff(c_843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_722, c_841])).
% 5.44/1.98  tff(c_844, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_361])).
% 5.44/1.98  tff(c_898, plain, (![A_137, B_138, C_139]: (k2_relset_1(A_137, B_138, C_139)=k2_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.44/1.98  tff(c_904, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_898])).
% 5.44/1.98  tff(c_911, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_844, c_904])).
% 5.44/1.98  tff(c_968, plain, (![C_143, A_144, B_145]: (v2_funct_1(C_143) | ~v3_funct_2(C_143, A_144, B_145) | ~v1_funct_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.44/1.98  tff(c_974, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_968])).
% 5.44/1.98  tff(c_982, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_974])).
% 5.44/1.98  tff(c_1480, plain, (![C_206, D_207, B_208, A_209]: (k2_funct_1(C_206)=D_207 | k1_xboole_0=B_208 | k1_xboole_0=A_209 | ~v2_funct_1(C_206) | ~r2_relset_1(A_209, A_209, k1_partfun1(A_209, B_208, B_208, A_209, C_206, D_207), k6_partfun1(A_209)) | k2_relset_1(A_209, B_208, C_206)!=B_208 | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(B_208, A_209))) | ~v1_funct_2(D_207, B_208, A_209) | ~v1_funct_1(D_207) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_209, B_208))) | ~v1_funct_2(C_206, A_209, B_208) | ~v1_funct_1(C_206))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.44/1.98  tff(c_1483, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_1480])).
% 5.44/1.98  tff(c_1489, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_66, c_62, c_911, c_982, c_1483])).
% 5.44/1.98  tff(c_1490, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_262, c_1489])).
% 5.44/1.98  tff(c_1193, plain, (![A_168, B_169]: (k2_funct_2(A_168, B_169)=k2_funct_1(B_169) | ~m1_subset_1(B_169, k1_zfmisc_1(k2_zfmisc_1(A_168, A_168))) | ~v3_funct_2(B_169, A_168, A_168) | ~v1_funct_2(B_169, A_168, A_168) | ~v1_funct_1(B_169))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.44/1.98  tff(c_1202, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1193])).
% 5.44/1.98  tff(c_1210, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_1202])).
% 5.44/1.98  tff(c_58, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.44/1.98  tff(c_1214, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1210, c_58])).
% 5.44/1.98  tff(c_1491, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1214])).
% 5.44/1.98  tff(c_1495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_890, c_1491])).
% 5.44/1.98  tff(c_1497, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_206])).
% 5.44/1.98  tff(c_6, plain, (![A_6]: (k2_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.44/1.98  tff(c_232, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_222, c_6])).
% 5.44/1.98  tff(c_242, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_232])).
% 5.44/1.98  tff(c_1499, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1497, c_242])).
% 5.44/1.98  tff(c_1599, plain, (![C_220, B_221, A_222]: (v5_relat_1(C_220, B_221) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_222, B_221))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.44/1.98  tff(c_1610, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_1599])).
% 5.44/1.98  tff(c_1663, plain, (![B_229, A_230]: (k2_relat_1(B_229)=A_230 | ~v2_funct_2(B_229, A_230) | ~v5_relat_1(B_229, A_230) | ~v1_relat_1(B_229))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.44/1.98  tff(c_1675, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1610, c_1663])).
% 5.44/1.98  tff(c_1688, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_1675])).
% 5.44/1.98  tff(c_1689, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1499, c_1688])).
% 5.44/1.98  tff(c_1847, plain, (![C_248, B_249, A_250]: (v2_funct_2(C_248, B_249) | ~v3_funct_2(C_248, A_250, B_249) | ~v1_funct_1(C_248) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_250, B_249))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.44/1.98  tff(c_1856, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1847])).
% 5.44/1.98  tff(c_1865, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1856])).
% 5.44/1.98  tff(c_1867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1689, c_1865])).
% 5.44/1.98  tff(c_1868, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_232])).
% 5.44/1.98  tff(c_1888, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2') | '#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1868, c_1868, c_206])).
% 5.44/1.98  tff(c_1889, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_1888])).
% 5.44/1.98  tff(c_1869, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_232])).
% 5.44/1.98  tff(c_1883, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1868, c_1869])).
% 5.44/1.98  tff(c_1995, plain, (![C_260, B_261, A_262]: (v5_relat_1(C_260, B_261) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_262, B_261))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.44/1.98  tff(c_2006, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_1995])).
% 5.44/1.98  tff(c_2039, plain, (![B_268, A_269]: (k2_relat_1(B_268)=A_269 | ~v2_funct_2(B_268, A_269) | ~v5_relat_1(B_268, A_269) | ~v1_relat_1(B_268))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.44/1.98  tff(c_2051, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2006, c_2039])).
% 5.44/1.98  tff(c_2063, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_1883, c_2051])).
% 5.44/1.98  tff(c_2064, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1889, c_2063])).
% 5.44/1.98  tff(c_2256, plain, (![C_287, B_288, A_289]: (v2_funct_2(C_287, B_288) | ~v3_funct_2(C_287, A_289, B_288) | ~v1_funct_1(C_287) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_289, B_288))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.44/1.98  tff(c_2265, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_2256])).
% 5.44/1.98  tff(c_2276, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_2265])).
% 5.44/1.98  tff(c_2278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2064, c_2276])).
% 5.44/1.98  tff(c_2280, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1888])).
% 5.44/1.98  tff(c_2283, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_1868])).
% 5.44/1.98  tff(c_175, plain, (![A_57]: (m1_subset_1(k6_partfun1(A_57), k1_zfmisc_1(k2_zfmisc_1(A_57, A_57))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.44/1.98  tff(c_178, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_9, A_9))) | k1_xboole_0!=A_9)), inference(superposition, [status(thm), theory('equality')], [c_124, c_175])).
% 5.44/1.98  tff(c_2873, plain, (![A_9]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_9, A_9))) | A_9!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2283, c_2283, c_178])).
% 5.44/1.98  tff(c_2970, plain, (![A_364, B_365, D_366]: (r2_relset_1(A_364, B_365, D_366, D_366) | ~m1_subset_1(D_366, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.44/1.98  tff(c_2987, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2873, c_2970])).
% 5.44/1.98  tff(c_2284, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_222])).
% 5.44/1.98  tff(c_2290, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_76])).
% 5.44/1.98  tff(c_1876, plain, (![A_9]: (A_9!='#skF_2' | k6_partfun1(A_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1868, c_1868, c_124])).
% 5.44/1.98  tff(c_2759, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_2280, c_1876])).
% 5.44/1.98  tff(c_126, plain, (![A_55]: (k1_xboole_0!=A_55 | k6_partfun1(A_55)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_121])).
% 5.44/1.98  tff(c_18, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.44/1.98  tff(c_79, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 5.44/1.98  tff(c_142, plain, (![A_55]: (v2_funct_1(k1_xboole_0) | k1_xboole_0!=A_55)), inference(superposition, [status(thm), theory('equality')], [c_126, c_79])).
% 5.44/1.98  tff(c_161, plain, (![A_55]: (k1_xboole_0!=A_55)), inference(splitLeft, [status(thm)], [c_142])).
% 5.44/1.98  tff(c_167, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_161])).
% 5.44/1.98  tff(c_168, plain, (v2_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_142])).
% 5.44/1.98  tff(c_1874, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1868, c_168])).
% 5.44/1.98  tff(c_2282, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_1874])).
% 5.44/1.98  tff(c_132, plain, (![A_55]: (k1_relat_1(k1_xboole_0)=A_55 | k1_xboole_0!=A_55)), inference(superposition, [status(thm), theory('equality')], [c_126, c_83])).
% 5.44/1.98  tff(c_1873, plain, (![A_55]: (k1_relat_1('#skF_2')=A_55 | A_55!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1868, c_1868, c_132])).
% 5.44/1.98  tff(c_2793, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_2280, c_1873])).
% 5.44/1.98  tff(c_2281, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_2280, c_1883])).
% 5.44/1.98  tff(c_14, plain, (![A_8]: (k5_relat_1(A_8, k6_relat_1(k2_relat_1(A_8)))=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.44/1.98  tff(c_81, plain, (![A_8]: (k5_relat_1(A_8, k6_partfun1(k2_relat_1(A_8)))=A_8 | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 5.44/1.98  tff(c_22, plain, (![A_13, B_15]: (k2_funct_1(A_13)=B_15 | k6_relat_1(k1_relat_1(A_13))!=k5_relat_1(A_13, B_15) | k2_relat_1(A_13)!=k1_relat_1(B_15) | ~v2_funct_1(A_13) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.44/1.98  tff(c_3292, plain, (![A_413, B_414]: (k2_funct_1(A_413)=B_414 | k6_partfun1(k1_relat_1(A_413))!=k5_relat_1(A_413, B_414) | k2_relat_1(A_413)!=k1_relat_1(B_414) | ~v2_funct_1(A_413) | ~v1_funct_1(B_414) | ~v1_relat_1(B_414) | ~v1_funct_1(A_413) | ~v1_relat_1(A_413))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_22])).
% 5.44/1.98  tff(c_3301, plain, (![A_8]: (k6_partfun1(k2_relat_1(A_8))=k2_funct_1(A_8) | k6_partfun1(k1_relat_1(A_8))!=A_8 | k1_relat_1(k6_partfun1(k2_relat_1(A_8)))!=k2_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(k6_partfun1(k2_relat_1(A_8))) | ~v1_relat_1(k6_partfun1(k2_relat_1(A_8))) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_81, c_3292])).
% 5.44/1.98  tff(c_3507, plain, (![A_428]: (k6_partfun1(k2_relat_1(A_428))=k2_funct_1(A_428) | k6_partfun1(k1_relat_1(A_428))!=A_428 | ~v2_funct_1(A_428) | ~v1_funct_1(k6_partfun1(k2_relat_1(A_428))) | ~v1_funct_1(A_428) | ~v1_relat_1(A_428))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_83, c_3301])).
% 5.44/1.98  tff(c_3516, plain, (k6_partfun1(k2_relat_1('#skF_1'))=k2_funct_1('#skF_1') | k6_partfun1(k1_relat_1('#skF_1'))!='#skF_1' | ~v2_funct_1('#skF_1') | ~v1_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2281, c_3507])).
% 5.44/1.98  tff(c_3523, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2284, c_2290, c_2290, c_2759, c_2282, c_2759, c_2793, c_2759, c_2281, c_3516])).
% 5.44/1.98  tff(c_2288, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_74])).
% 5.44/1.98  tff(c_2289, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_72])).
% 5.44/1.98  tff(c_3229, plain, (![A_401, B_402]: (k2_funct_2(A_401, B_402)=k2_funct_1(B_402) | ~m1_subset_1(B_402, k1_zfmisc_1(k2_zfmisc_1(A_401, A_401))) | ~v3_funct_2(B_402, A_401, A_401) | ~v1_funct_2(B_402, A_401, A_401) | ~v1_funct_1(B_402))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.44/1.98  tff(c_3232, plain, (![A_9]: (k2_funct_2(A_9, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_9, A_9) | ~v1_funct_2('#skF_1', A_9, A_9) | ~v1_funct_1('#skF_1') | A_9!='#skF_1')), inference(resolution, [status(thm)], [c_2873, c_3229])).
% 5.44/1.98  tff(c_3241, plain, (![A_403]: (k2_funct_2(A_403, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_403, A_403) | ~v1_funct_2('#skF_1', A_403, A_403) | A_403!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2290, c_3232])).
% 5.44/1.98  tff(c_3244, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2289, c_3241])).
% 5.44/1.98  tff(c_3247, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2288, c_3244])).
% 5.44/1.98  tff(c_216, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_207])).
% 5.44/1.98  tff(c_225, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_216])).
% 5.44/1.98  tff(c_240, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_225, c_6])).
% 5.44/1.98  tff(c_2329, plain, (k2_relat_1('#skF_3')!='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2283, c_2283, c_240])).
% 5.44/1.98  tff(c_2330, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2329])).
% 5.44/1.98  tff(c_2367, plain, (![C_293, B_294, A_295]: (v5_relat_1(C_293, B_294) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_295, B_294))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.44/1.98  tff(c_2379, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_2367])).
% 5.44/1.98  tff(c_2568, plain, (![B_313, A_314]: (k2_relat_1(B_313)=A_314 | ~v2_funct_2(B_313, A_314) | ~v5_relat_1(B_313, A_314) | ~v1_relat_1(B_313))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.44/1.98  tff(c_2577, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2379, c_2568])).
% 5.44/1.98  tff(c_2586, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_2577])).
% 5.44/1.98  tff(c_2587, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2330, c_2586])).
% 5.44/1.98  tff(c_64, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.44/1.98  tff(c_2716, plain, (![C_336, B_337, A_338]: (v2_funct_2(C_336, B_337) | ~v3_funct_2(C_336, A_338, B_337) | ~v1_funct_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_338, B_337))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.44/1.98  tff(c_2725, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2716])).
% 5.44/1.98  tff(c_2733, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2725])).
% 5.44/1.98  tff(c_2735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2587, c_2733])).
% 5.44/1.98  tff(c_2736, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2329])).
% 5.44/1.98  tff(c_2286, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_58])).
% 5.44/1.98  tff(c_2756, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2736, c_2286])).
% 5.44/1.98  tff(c_3248, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3247, c_2756])).
% 5.44/1.98  tff(c_3529, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3523, c_3248])).
% 5.44/1.98  tff(c_3536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2987, c_3529])).
% 5.44/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/1.98  
% 5.44/1.98  Inference rules
% 5.44/1.98  ----------------------
% 5.44/1.98  #Ref     : 13
% 5.44/1.98  #Sup     : 721
% 5.44/1.98  #Fact    : 0
% 5.44/1.98  #Define  : 0
% 5.44/1.98  #Split   : 25
% 5.44/1.98  #Chain   : 0
% 5.44/1.98  #Close   : 0
% 5.44/1.98  
% 5.44/1.98  Ordering : KBO
% 5.44/1.98  
% 5.44/1.98  Simplification rules
% 5.44/1.98  ----------------------
% 5.44/1.98  #Subsume      : 134
% 5.44/1.98  #Demod        : 820
% 5.44/1.98  #Tautology    : 342
% 5.44/1.98  #SimpNegUnit  : 18
% 5.44/1.98  #BackRed      : 55
% 5.44/1.98  
% 5.44/1.98  #Partial instantiations: 0
% 5.44/1.98  #Strategies tried      : 1
% 5.44/1.98  
% 5.44/1.98  Timing (in seconds)
% 5.44/1.98  ----------------------
% 5.44/1.98  Preprocessing        : 0.37
% 5.44/1.98  Parsing              : 0.20
% 5.44/1.98  CNF conversion       : 0.02
% 5.44/1.99  Main loop            : 0.82
% 5.44/1.99  Inferencing          : 0.28
% 5.44/1.99  Reduction            : 0.31
% 5.44/1.99  Demodulation         : 0.22
% 5.44/1.99  BG Simplification    : 0.03
% 5.44/1.99  Subsumption          : 0.13
% 5.44/1.99  Abstraction          : 0.03
% 5.44/1.99  MUC search           : 0.00
% 5.44/1.99  Cooper               : 0.00
% 5.44/1.99  Total                : 1.24
% 5.44/1.99  Index Insertion      : 0.00
% 5.44/1.99  Index Deletion       : 0.00
% 5.44/1.99  Index Matching       : 0.00
% 5.44/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
