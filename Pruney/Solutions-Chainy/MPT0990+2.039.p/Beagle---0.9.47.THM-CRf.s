%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:01 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 581 expanded)
%              Number of leaves         :   41 ( 226 expanded)
%              Depth                    :   18
%              Number of atoms          :  291 (2560 expanded)
%              Number of equality atoms :  108 ( 947 expanded)
%              Maximal formula depth    :   16 (   4 average)
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

tff(f_187,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_118,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
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

tff(f_106,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

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

tff(f_135,axiom,(
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

tff(f_27,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_161,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_52,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_93,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_105,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_93])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_135,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_147,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_135])).

tff(c_243,plain,(
    ! [B_80,A_81,C_82] :
      ( k1_xboole_0 = B_80
      | k1_relset_1(A_81,B_80,C_82) = A_81
      | ~ v1_funct_2(C_82,A_81,B_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_252,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_243])).

tff(c_261,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_147,c_252])).

tff(c_262,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_261])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_93])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_146,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_135])).

tff(c_249,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_243])).

tff(c_257,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_146,c_249])).

tff(c_258,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_257])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_165,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_171,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_165])).

tff(c_177,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_171])).

tff(c_40,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4,plain,(
    ! [A_2,B_4] :
      ( k2_funct_1(A_2) = B_4
      | k6_relat_1(k2_relat_1(A_2)) != k5_relat_1(B_4,A_2)
      | k2_relat_1(B_4) != k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_520,plain,(
    ! [A_125,B_126] :
      ( k2_funct_1(A_125) = B_126
      | k6_partfun1(k2_relat_1(A_125)) != k5_relat_1(B_126,A_125)
      | k2_relat_1(B_126) != k1_relat_1(A_125)
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_522,plain,(
    ! [B_126] :
      ( k2_funct_1('#skF_3') = B_126
      | k5_relat_1(B_126,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_126) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_520])).

tff(c_525,plain,(
    ! [B_127] :
      ( k2_funct_1('#skF_3') = B_127
      | k5_relat_1(B_127,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_127) != '#skF_1'
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_74,c_58,c_258,c_522])).

tff(c_531,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_525])).

tff(c_538,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_531])).

tff(c_539,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_538])).

tff(c_543,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_539])).

tff(c_36,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_124,plain,(
    ! [A_57,B_58,D_59] :
      ( r2_relset_1(A_57,B_58,D_59,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_131,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_36,c_124])).

tff(c_178,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_165])).

tff(c_446,plain,(
    ! [E_121,A_119,D_123,B_124,C_120,F_122] :
      ( m1_subset_1(k1_partfun1(A_119,B_124,C_120,D_123,E_121,F_122),k1_zfmisc_1(k2_zfmisc_1(A_119,D_123)))
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_120,D_123)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_124)))
      | ~ v1_funct_1(E_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_273,plain,(
    ! [D_83,C_84,A_85,B_86] :
      ( D_83 = C_84
      | ~ r2_relset_1(A_85,B_86,C_84,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_281,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_273])).

tff(c_296,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_281])).

tff(c_310,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_465,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_446,c_310])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_465])).

tff(c_511,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_1055,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( k2_relset_1(A_172,B_173,C_174) = B_173
      | ~ r2_relset_1(B_173,B_173,k1_partfun1(B_173,A_172,A_172,B_173,D_175,C_174),k6_partfun1(B_173))
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k2_zfmisc_1(B_173,A_172)))
      | ~ v1_funct_2(D_175,B_173,A_172)
      | ~ v1_funct_1(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_2(C_174,A_172,B_173)
      | ~ v1_funct_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1061,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_1055])).

tff(c_1065,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_131,c_178,c_1061])).

tff(c_1067,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_543,c_1065])).

tff(c_1069,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_539])).

tff(c_75,plain,(
    ! [A_2,B_4] :
      ( k2_funct_1(A_2) = B_4
      | k6_partfun1(k2_relat_1(A_2)) != k5_relat_1(B_4,A_2)
      | k2_relat_1(B_4) != k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_1073,plain,(
    ! [B_4] :
      ( k2_funct_1('#skF_4') = B_4
      | k5_relat_1(B_4,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_4) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1069,c_75])).

tff(c_1077,plain,(
    ! [B_4] :
      ( k2_funct_1('#skF_4') = B_4
      | k5_relat_1(B_4,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_4) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_68,c_262,c_1073])).

tff(c_1085,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1077])).

tff(c_2,plain,(
    ! [A_1] : v2_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_1] : v2_funct_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2])).

tff(c_1416,plain,(
    ! [D_217,C_216,A_215,B_218,E_214] :
      ( k1_xboole_0 = C_216
      | v2_funct_1(E_214)
      | k2_relset_1(A_215,B_218,D_217) != B_218
      | ~ v2_funct_1(k1_partfun1(A_215,B_218,B_218,C_216,D_217,E_214))
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(B_218,C_216)))
      | ~ v1_funct_2(E_214,B_218,C_216)
      | ~ v1_funct_1(E_214)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_218)))
      | ~ v1_funct_2(D_217,A_215,B_218)
      | ~ v1_funct_1(D_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1418,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_511,c_1416])).

tff(c_1420,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_76,c_62,c_1418])).

tff(c_1422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1085,c_56,c_1420])).

tff(c_1424,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1077])).

tff(c_1425,plain,(
    ! [B_219] :
      ( k2_funct_1('#skF_4') = B_219
      | k5_relat_1(B_219,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_219) != '#skF_2'
      | ~ v1_funct_1(B_219)
      | ~ v1_relat_1(B_219) ) ),
    inference(splitRight,[status(thm)],[c_1077])).

tff(c_1434,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_1425])).

tff(c_1441,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_177,c_1434])).

tff(c_1442,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1441])).

tff(c_1475,plain,(
    ! [E_234,A_232,C_235,B_231,D_230,F_233] :
      ( k1_partfun1(A_232,B_231,C_235,D_230,E_234,F_233) = k5_relat_1(E_234,F_233)
      | ~ m1_subset_1(F_233,k1_zfmisc_1(k2_zfmisc_1(C_235,D_230)))
      | ~ v1_funct_1(F_233)
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_231)))
      | ~ v1_funct_1(E_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1481,plain,(
    ! [A_232,B_231,E_234] :
      ( k1_partfun1(A_232,B_231,'#skF_2','#skF_1',E_234,'#skF_4') = k5_relat_1(E_234,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_231)))
      | ~ v1_funct_1(E_234) ) ),
    inference(resolution,[status(thm)],[c_64,c_1475])).

tff(c_1576,plain,(
    ! [A_247,B_248,E_249] :
      ( k1_partfun1(A_247,B_248,'#skF_2','#skF_1',E_249,'#skF_4') = k5_relat_1(E_249,'#skF_4')
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ v1_funct_1(E_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1481])).

tff(c_1585,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1576])).

tff(c_1593,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_511,c_1585])).

tff(c_1595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1442,c_1593])).

tff(c_1596,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1441])).

tff(c_6,plain,(
    ! [A_5] :
      ( k2_funct_1(k2_funct_1(A_5)) = A_5
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1602,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1596,c_6])).

tff(c_1606,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_68,c_1424,c_1602])).

tff(c_1608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.79  
% 4.32/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.79  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.32/1.79  
% 4.32/1.79  %Foreground sorts:
% 4.32/1.79  
% 4.32/1.79  
% 4.32/1.79  %Background operators:
% 4.32/1.79  
% 4.32/1.79  
% 4.32/1.79  %Foreground operators:
% 4.32/1.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.32/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.32/1.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.32/1.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.32/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.79  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.32/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.32/1.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.32/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.32/1.79  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.32/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.32/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.32/1.79  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.32/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.32/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.32/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.32/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.32/1.79  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.32/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.32/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.32/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.32/1.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.32/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.32/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.32/1.79  
% 4.70/1.82  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.70/1.82  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.70/1.82  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.70/1.82  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.70/1.82  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.70/1.82  tff(f_118, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.70/1.82  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.70/1.82  tff(f_106, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.70/1.82  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.70/1.82  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.70/1.82  tff(f_135, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.70/1.82  tff(f_27, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 4.70/1.82  tff(f_161, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 4.70/1.82  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.70/1.82  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 4.70/1.82  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_93, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.70/1.82  tff(c_105, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_93])).
% 4.70/1.82  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_135, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.70/1.82  tff(c_147, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_135])).
% 4.70/1.82  tff(c_243, plain, (![B_80, A_81, C_82]: (k1_xboole_0=B_80 | k1_relset_1(A_81, B_80, C_82)=A_81 | ~v1_funct_2(C_82, A_81, B_80) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.70/1.82  tff(c_252, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_243])).
% 4.70/1.82  tff(c_261, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_147, c_252])).
% 4.70/1.82  tff(c_262, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_261])).
% 4.70/1.82  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_93])).
% 4.70/1.82  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_146, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_135])).
% 4.70/1.82  tff(c_249, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_243])).
% 4.70/1.82  tff(c_257, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_146, c_249])).
% 4.70/1.82  tff(c_258, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_257])).
% 4.70/1.82  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_165, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.70/1.82  tff(c_171, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_165])).
% 4.70/1.82  tff(c_177, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_171])).
% 4.70/1.82  tff(c_40, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.70/1.82  tff(c_4, plain, (![A_2, B_4]: (k2_funct_1(A_2)=B_4 | k6_relat_1(k2_relat_1(A_2))!=k5_relat_1(B_4, A_2) | k2_relat_1(B_4)!=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.70/1.82  tff(c_520, plain, (![A_125, B_126]: (k2_funct_1(A_125)=B_126 | k6_partfun1(k2_relat_1(A_125))!=k5_relat_1(B_126, A_125) | k2_relat_1(B_126)!=k1_relat_1(A_125) | ~v2_funct_1(A_125) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4])).
% 4.70/1.82  tff(c_522, plain, (![B_126]: (k2_funct_1('#skF_3')=B_126 | k5_relat_1(B_126, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_126)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_520])).
% 4.70/1.82  tff(c_525, plain, (![B_127]: (k2_funct_1('#skF_3')=B_127 | k5_relat_1(B_127, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_127)!='#skF_1' | ~v1_funct_1(B_127) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_74, c_58, c_258, c_522])).
% 4.70/1.82  tff(c_531, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_105, c_525])).
% 4.70/1.82  tff(c_538, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_531])).
% 4.70/1.82  tff(c_539, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_538])).
% 4.70/1.82  tff(c_543, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_539])).
% 4.70/1.82  tff(c_36, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.70/1.82  tff(c_124, plain, (![A_57, B_58, D_59]: (r2_relset_1(A_57, B_58, D_59, D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.70/1.82  tff(c_131, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_36, c_124])).
% 4.70/1.82  tff(c_178, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_165])).
% 4.70/1.82  tff(c_446, plain, (![E_121, A_119, D_123, B_124, C_120, F_122]: (m1_subset_1(k1_partfun1(A_119, B_124, C_120, D_123, E_121, F_122), k1_zfmisc_1(k2_zfmisc_1(A_119, D_123))) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_120, D_123))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_124))) | ~v1_funct_1(E_121))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.70/1.82  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.70/1.82  tff(c_273, plain, (![D_83, C_84, A_85, B_86]: (D_83=C_84 | ~r2_relset_1(A_85, B_86, C_84, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.70/1.82  tff(c_281, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_273])).
% 4.70/1.82  tff(c_296, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_281])).
% 4.70/1.82  tff(c_310, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_296])).
% 4.70/1.82  tff(c_465, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_446, c_310])).
% 4.70/1.82  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_465])).
% 4.70/1.82  tff(c_511, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_296])).
% 4.70/1.82  tff(c_1055, plain, (![A_172, B_173, C_174, D_175]: (k2_relset_1(A_172, B_173, C_174)=B_173 | ~r2_relset_1(B_173, B_173, k1_partfun1(B_173, A_172, A_172, B_173, D_175, C_174), k6_partfun1(B_173)) | ~m1_subset_1(D_175, k1_zfmisc_1(k2_zfmisc_1(B_173, A_172))) | ~v1_funct_2(D_175, B_173, A_172) | ~v1_funct_1(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_2(C_174, A_172, B_173) | ~v1_funct_1(C_174))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.70/1.82  tff(c_1061, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_511, c_1055])).
% 4.70/1.82  tff(c_1065, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_131, c_178, c_1061])).
% 4.70/1.82  tff(c_1067, plain, $false, inference(negUnitSimplification, [status(thm)], [c_543, c_1065])).
% 4.70/1.82  tff(c_1069, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_539])).
% 4.70/1.82  tff(c_75, plain, (![A_2, B_4]: (k2_funct_1(A_2)=B_4 | k6_partfun1(k2_relat_1(A_2))!=k5_relat_1(B_4, A_2) | k2_relat_1(B_4)!=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4])).
% 4.70/1.82  tff(c_1073, plain, (![B_4]: (k2_funct_1('#skF_4')=B_4 | k5_relat_1(B_4, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_4)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1069, c_75])).
% 4.70/1.82  tff(c_1077, plain, (![B_4]: (k2_funct_1('#skF_4')=B_4 | k5_relat_1(B_4, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_4)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_68, c_262, c_1073])).
% 4.70/1.82  tff(c_1085, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1077])).
% 4.70/1.82  tff(c_2, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.70/1.82  tff(c_76, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2])).
% 4.70/1.82  tff(c_1416, plain, (![D_217, C_216, A_215, B_218, E_214]: (k1_xboole_0=C_216 | v2_funct_1(E_214) | k2_relset_1(A_215, B_218, D_217)!=B_218 | ~v2_funct_1(k1_partfun1(A_215, B_218, B_218, C_216, D_217, E_214)) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(B_218, C_216))) | ~v1_funct_2(E_214, B_218, C_216) | ~v1_funct_1(E_214) | ~m1_subset_1(D_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_218))) | ~v1_funct_2(D_217, A_215, B_218) | ~v1_funct_1(D_217))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.70/1.82  tff(c_1418, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_511, c_1416])).
% 4.70/1.82  tff(c_1420, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_76, c_62, c_1418])).
% 4.70/1.82  tff(c_1422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1085, c_56, c_1420])).
% 4.70/1.82  tff(c_1424, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1077])).
% 4.70/1.82  tff(c_1425, plain, (![B_219]: (k2_funct_1('#skF_4')=B_219 | k5_relat_1(B_219, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_219)!='#skF_2' | ~v1_funct_1(B_219) | ~v1_relat_1(B_219))), inference(splitRight, [status(thm)], [c_1077])).
% 4.70/1.82  tff(c_1434, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_1425])).
% 4.70/1.82  tff(c_1441, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_177, c_1434])).
% 4.70/1.82  tff(c_1442, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1441])).
% 4.70/1.82  tff(c_1475, plain, (![E_234, A_232, C_235, B_231, D_230, F_233]: (k1_partfun1(A_232, B_231, C_235, D_230, E_234, F_233)=k5_relat_1(E_234, F_233) | ~m1_subset_1(F_233, k1_zfmisc_1(k2_zfmisc_1(C_235, D_230))) | ~v1_funct_1(F_233) | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_231))) | ~v1_funct_1(E_234))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.70/1.82  tff(c_1481, plain, (![A_232, B_231, E_234]: (k1_partfun1(A_232, B_231, '#skF_2', '#skF_1', E_234, '#skF_4')=k5_relat_1(E_234, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_231))) | ~v1_funct_1(E_234))), inference(resolution, [status(thm)], [c_64, c_1475])).
% 4.70/1.82  tff(c_1576, plain, (![A_247, B_248, E_249]: (k1_partfun1(A_247, B_248, '#skF_2', '#skF_1', E_249, '#skF_4')=k5_relat_1(E_249, '#skF_4') | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~v1_funct_1(E_249))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1481])).
% 4.70/1.82  tff(c_1585, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1576])).
% 4.70/1.82  tff(c_1593, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_511, c_1585])).
% 4.70/1.82  tff(c_1595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1442, c_1593])).
% 4.70/1.82  tff(c_1596, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1441])).
% 4.70/1.82  tff(c_6, plain, (![A_5]: (k2_funct_1(k2_funct_1(A_5))=A_5 | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.70/1.82  tff(c_1602, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1596, c_6])).
% 4.70/1.82  tff(c_1606, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_68, c_1424, c_1602])).
% 4.70/1.82  tff(c_1608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1606])).
% 4.70/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.82  
% 4.70/1.82  Inference rules
% 4.70/1.82  ----------------------
% 4.70/1.82  #Ref     : 0
% 4.70/1.82  #Sup     : 335
% 4.70/1.82  #Fact    : 0
% 4.70/1.82  #Define  : 0
% 4.70/1.82  #Split   : 18
% 4.70/1.82  #Chain   : 0
% 4.70/1.82  #Close   : 0
% 4.70/1.82  
% 4.70/1.82  Ordering : KBO
% 4.70/1.82  
% 4.70/1.82  Simplification rules
% 4.70/1.82  ----------------------
% 4.70/1.82  #Subsume      : 4
% 4.70/1.82  #Demod        : 242
% 4.70/1.82  #Tautology    : 92
% 4.70/1.82  #SimpNegUnit  : 29
% 4.70/1.82  #BackRed      : 14
% 4.70/1.82  
% 4.70/1.82  #Partial instantiations: 0
% 4.70/1.82  #Strategies tried      : 1
% 4.70/1.82  
% 4.70/1.82  Timing (in seconds)
% 4.70/1.82  ----------------------
% 4.70/1.82  Preprocessing        : 0.40
% 4.70/1.82  Parsing              : 0.21
% 4.70/1.82  CNF conversion       : 0.03
% 4.70/1.82  Main loop            : 0.63
% 4.70/1.82  Inferencing          : 0.22
% 4.70/1.82  Reduction            : 0.22
% 4.70/1.82  Demodulation         : 0.14
% 4.70/1.82  BG Simplification    : 0.03
% 4.70/1.82  Subsumption          : 0.11
% 4.70/1.82  Abstraction          : 0.03
% 4.70/1.82  MUC search           : 0.00
% 4.70/1.82  Cooper               : 0.00
% 4.70/1.82  Total                : 1.08
% 4.70/1.82  Index Insertion      : 0.00
% 4.70/1.82  Index Deletion       : 0.00
% 4.70/1.82  Index Matching       : 0.00
% 4.70/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
