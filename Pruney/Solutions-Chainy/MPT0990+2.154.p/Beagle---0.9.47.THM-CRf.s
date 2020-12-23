%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:19 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 911 expanded)
%              Number of leaves         :   43 ( 341 expanded)
%              Depth                    :   17
%              Number of atoms          :  348 (3864 expanded)
%              Number of equality atoms :  126 (1386 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_205,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_74,axiom,(
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

tff(f_124,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_134,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_153,axiom,(
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

tff(f_179,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_57,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_55,axiom,(
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

tff(f_169,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_62,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_124,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_133,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_74,c_124])).

tff(c_142,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_133])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_130,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_124])).

tff(c_139,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_130])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_82,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_237,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_253,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_237])).

tff(c_383,plain,(
    ! [B_87,A_88,C_89] :
      ( k1_xboole_0 = B_87
      | k1_relset_1(A_88,B_87,C_89) = A_88
      | ~ v1_funct_2(C_89,A_88,B_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_395,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_383])).

tff(c_408,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_253,c_395])).

tff(c_409,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_408])).

tff(c_72,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_199,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_208,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_199])).

tff(c_216,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_208])).

tff(c_48,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_16,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_relat_1(k2_relat_1(A_11)) != k5_relat_1(B_13,A_11)
      | k2_relat_1(B_13) != k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1080,plain,(
    ! [A_149,B_150] :
      ( k2_funct_1(A_149) = B_150
      | k6_partfun1(k2_relat_1(A_149)) != k5_relat_1(B_150,A_149)
      | k2_relat_1(B_150) != k1_relat_1(A_149)
      | ~ v2_funct_1(A_149)
      | ~ v1_funct_1(B_150)
      | ~ v1_relat_1(B_150)
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_1082,plain,(
    ! [B_150] :
      ( k2_funct_1('#skF_3') = B_150
      | k5_relat_1(B_150,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_150) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_150)
      | ~ v1_relat_1(B_150)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_1080])).

tff(c_1089,plain,(
    ! [B_151] :
      ( k2_funct_1('#skF_3') = B_151
      | k5_relat_1(B_151,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_151) != '#skF_1'
      | ~ v1_funct_1(B_151)
      | ~ v1_relat_1(B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_84,c_68,c_409,c_1082])).

tff(c_1095,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_1089])).

tff(c_1106,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1095])).

tff(c_1107,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1106])).

tff(c_1112,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1107])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_44,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_156,plain,(
    ! [A_64,B_65,D_66] :
      ( r2_relset_1(A_64,B_65,D_66,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_163,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_44,c_156])).

tff(c_217,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_199])).

tff(c_704,plain,(
    ! [C_121,E_119,A_116,F_118,B_120,D_117] :
      ( k1_partfun1(A_116,B_120,C_121,D_117,E_119,F_118) = k5_relat_1(E_119,F_118)
      | ~ m1_subset_1(F_118,k1_zfmisc_1(k2_zfmisc_1(C_121,D_117)))
      | ~ v1_funct_1(F_118)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_116,B_120)))
      | ~ v1_funct_1(E_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_714,plain,(
    ! [A_116,B_120,E_119] :
      ( k1_partfun1(A_116,B_120,'#skF_2','#skF_1',E_119,'#skF_4') = k5_relat_1(E_119,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_116,B_120)))
      | ~ v1_funct_1(E_119) ) ),
    inference(resolution,[status(thm)],[c_74,c_704])).

tff(c_849,plain,(
    ! [A_134,B_135,E_136] :
      ( k1_partfun1(A_134,B_135,'#skF_2','#skF_1',E_136,'#skF_4') = k5_relat_1(E_136,'#skF_4')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_714])).

tff(c_861,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_849])).

tff(c_872,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_861])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_559,plain,(
    ! [D_98,C_99,A_100,B_101] :
      ( D_98 = C_99
      | ~ r2_relset_1(A_100,B_101,C_99,D_98)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_571,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_559])).

tff(c_592,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_571])).

tff(c_593,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_877,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_593])).

tff(c_976,plain,(
    ! [C_144,B_147,D_145,F_143,A_148,E_146] :
      ( m1_subset_1(k1_partfun1(A_148,B_147,C_144,D_145,E_146,F_143),k1_zfmisc_1(k2_zfmisc_1(A_148,D_145)))
      | ~ m1_subset_1(F_143,k1_zfmisc_1(k2_zfmisc_1(C_144,D_145)))
      | ~ v1_funct_1(F_143)
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147)))
      | ~ v1_funct_1(E_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1040,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_976])).

tff(c_1068,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_1040])).

tff(c_1070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_877,c_1068])).

tff(c_1071,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_2126,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( k2_relset_1(A_207,B_208,C_209) = B_208
      | ~ r2_relset_1(B_208,B_208,k1_partfun1(B_208,A_207,A_207,B_208,D_210,C_209),k6_partfun1(B_208))
      | ~ m1_subset_1(D_210,k1_zfmisc_1(k2_zfmisc_1(B_208,A_207)))
      | ~ v1_funct_2(D_210,B_208,A_207)
      | ~ v1_funct_1(D_210)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_2(C_209,A_207,B_208)
      | ~ v1_funct_1(C_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2132,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1071,c_2126])).

tff(c_2136,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_84,c_82,c_80,c_163,c_217,c_2132])).

tff(c_2138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1112,c_2136])).

tff(c_2139,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1107])).

tff(c_2140,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1107])).

tff(c_254,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_237])).

tff(c_398,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_383])).

tff(c_412,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_254,c_398])).

tff(c_413,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_412])).

tff(c_56,plain,(
    ! [A_49] :
      ( m1_subset_1(A_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_49),k2_relat_1(A_49))))
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_212,plain,(
    ! [A_49] :
      ( k2_relset_1(k1_relat_1(A_49),k2_relat_1(A_49),A_49) = k2_relat_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_56,c_199])).

tff(c_457,plain,
    ( k2_relset_1('#skF_2',k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_212])).

tff(c_473,plain,(
    k2_relset_1('#skF_2',k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_78,c_457])).

tff(c_2141,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2140,c_2140,c_473])).

tff(c_85,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_partfun1(k2_relat_1(A_11)) != k5_relat_1(B_13,A_11)
      | k2_relat_1(B_13) != k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_2153,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2140,c_85])).

tff(c_2172,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_78,c_413,c_2153])).

tff(c_2192,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2172])).

tff(c_14,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_2288,plain,(
    ! [D_227,C_231,F_228,E_229,A_226,B_230] :
      ( k1_partfun1(A_226,B_230,C_231,D_227,E_229,F_228) = k5_relat_1(E_229,F_228)
      | ~ m1_subset_1(F_228,k1_zfmisc_1(k2_zfmisc_1(C_231,D_227)))
      | ~ v1_funct_1(F_228)
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_226,B_230)))
      | ~ v1_funct_1(E_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2296,plain,(
    ! [A_226,B_230,E_229] :
      ( k1_partfun1(A_226,B_230,'#skF_2','#skF_1',E_229,'#skF_4') = k5_relat_1(E_229,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_226,B_230)))
      | ~ v1_funct_1(E_229) ) ),
    inference(resolution,[status(thm)],[c_74,c_2288])).

tff(c_2307,plain,(
    ! [A_233,B_234,E_235] :
      ( k1_partfun1(A_233,B_234,'#skF_2','#skF_1',E_235,'#skF_4') = k5_relat_1(E_235,'#skF_4')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2296])).

tff(c_2316,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_2307])).

tff(c_2324,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1071,c_2316])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( v2_funct_1(A_7)
      | k2_relat_1(B_9) != k1_relat_1(A_7)
      | ~ v2_funct_1(k5_relat_1(B_9,A_7))
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2331,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2324,c_10])).

tff(c_2338,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_78,c_139,c_84,c_86,c_216,c_413,c_2331])).

tff(c_2340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2192,c_2338])).

tff(c_2342,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2172])).

tff(c_2343,plain,(
    ! [B_236] :
      ( k2_funct_1('#skF_4') = B_236
      | k5_relat_1(B_236,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_236) != '#skF_2'
      | ~ v1_funct_1(B_236)
      | ~ v1_relat_1(B_236) ) ),
    inference(splitRight,[status(thm)],[c_2172])).

tff(c_2352,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_2343])).

tff(c_2363,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_216,c_2352])).

tff(c_2365,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2363])).

tff(c_2467,plain,(
    ! [D_253,A_252,E_255,B_256,F_254,C_257] :
      ( k1_partfun1(A_252,B_256,C_257,D_253,E_255,F_254) = k5_relat_1(E_255,F_254)
      | ~ m1_subset_1(F_254,k1_zfmisc_1(k2_zfmisc_1(C_257,D_253)))
      | ~ v1_funct_1(F_254)
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(A_252,B_256)))
      | ~ v1_funct_1(E_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2475,plain,(
    ! [A_252,B_256,E_255] :
      ( k1_partfun1(A_252,B_256,'#skF_2','#skF_1',E_255,'#skF_4') = k5_relat_1(E_255,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(A_252,B_256)))
      | ~ v1_funct_1(E_255) ) ),
    inference(resolution,[status(thm)],[c_74,c_2467])).

tff(c_2486,plain,(
    ! [A_259,B_260,E_261] :
      ( k1_partfun1(A_259,B_260,'#skF_2','#skF_1',E_261,'#skF_4') = k5_relat_1(E_261,'#skF_4')
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260)))
      | ~ v1_funct_1(E_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2475])).

tff(c_2495,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_2486])).

tff(c_2503,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1071,c_2495])).

tff(c_2505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2365,c_2503])).

tff(c_2506,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2363])).

tff(c_2737,plain,(
    ! [A_290,C_291,B_292] :
      ( k6_partfun1(A_290) = k5_relat_1(C_291,k2_funct_1(C_291))
      | k1_xboole_0 = B_292
      | ~ v2_funct_1(C_291)
      | k2_relset_1(A_290,B_292,C_291) != B_292
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_290,B_292)))
      | ~ v1_funct_2(C_291,A_290,B_292)
      | ~ v1_funct_1(C_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2745,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_2737])).

tff(c_2756,plain,
    ( k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2141,c_2342,c_2506,c_2745])).

tff(c_2758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2139,c_2756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.89/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.90  
% 4.89/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.90  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.89/1.90  
% 4.89/1.90  %Foreground sorts:
% 4.89/1.90  
% 4.89/1.90  
% 4.89/1.90  %Background operators:
% 4.89/1.90  
% 4.89/1.90  
% 4.89/1.90  %Foreground operators:
% 4.89/1.90  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.89/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.89/1.90  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.89/1.90  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.89/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.89/1.90  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.89/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.89/1.90  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.89/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.89/1.90  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.89/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.89/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.89/1.90  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.89/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.89/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.89/1.90  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.89/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.89/1.90  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.89/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.89/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.89/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.89/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.89/1.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.89/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.89/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.89/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.89/1.90  
% 4.89/1.93  tff(f_205, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.89/1.93  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.89/1.93  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.89/1.93  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.89/1.93  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.89/1.93  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.89/1.93  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.89/1.93  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.89/1.93  tff(f_124, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.89/1.93  tff(f_90, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.89/1.93  tff(f_134, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.89/1.93  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.89/1.93  tff(f_153, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.89/1.93  tff(f_179, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.89/1.93  tff(f_57, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 4.89/1.93  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.89/1.93  tff(f_169, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 4.89/1.93  tff(c_66, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_62, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.89/1.93  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_124, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.89/1.93  tff(c_133, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_74, c_124])).
% 4.89/1.93  tff(c_142, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_133])).
% 4.89/1.93  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_130, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_124])).
% 4.89/1.93  tff(c_139, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_130])).
% 4.89/1.93  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_82, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_237, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.89/1.93  tff(c_253, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_237])).
% 4.89/1.93  tff(c_383, plain, (![B_87, A_88, C_89]: (k1_xboole_0=B_87 | k1_relset_1(A_88, B_87, C_89)=A_88 | ~v1_funct_2(C_89, A_88, B_87) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.89/1.93  tff(c_395, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_383])).
% 4.89/1.93  tff(c_408, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_253, c_395])).
% 4.89/1.93  tff(c_409, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_408])).
% 4.89/1.93  tff(c_72, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_199, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.89/1.93  tff(c_208, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_199])).
% 4.89/1.93  tff(c_216, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_208])).
% 4.89/1.93  tff(c_48, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.89/1.93  tff(c_16, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_relat_1(k2_relat_1(A_11))!=k5_relat_1(B_13, A_11) | k2_relat_1(B_13)!=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.89/1.93  tff(c_1080, plain, (![A_149, B_150]: (k2_funct_1(A_149)=B_150 | k6_partfun1(k2_relat_1(A_149))!=k5_relat_1(B_150, A_149) | k2_relat_1(B_150)!=k1_relat_1(A_149) | ~v2_funct_1(A_149) | ~v1_funct_1(B_150) | ~v1_relat_1(B_150) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 4.89/1.93  tff(c_1082, plain, (![B_150]: (k2_funct_1('#skF_3')=B_150 | k5_relat_1(B_150, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_150)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_150) | ~v1_relat_1(B_150) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_216, c_1080])).
% 4.89/1.93  tff(c_1089, plain, (![B_151]: (k2_funct_1('#skF_3')=B_151 | k5_relat_1(B_151, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_151)!='#skF_1' | ~v1_funct_1(B_151) | ~v1_relat_1(B_151))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_84, c_68, c_409, c_1082])).
% 4.89/1.93  tff(c_1095, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_142, c_1089])).
% 4.89/1.93  tff(c_1106, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1095])).
% 4.89/1.93  tff(c_1107, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_1106])).
% 4.89/1.93  tff(c_1112, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1107])).
% 4.89/1.93  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_44, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.89/1.93  tff(c_156, plain, (![A_64, B_65, D_66]: (r2_relset_1(A_64, B_65, D_66, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.89/1.93  tff(c_163, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_44, c_156])).
% 4.89/1.93  tff(c_217, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_199])).
% 4.89/1.93  tff(c_704, plain, (![C_121, E_119, A_116, F_118, B_120, D_117]: (k1_partfun1(A_116, B_120, C_121, D_117, E_119, F_118)=k5_relat_1(E_119, F_118) | ~m1_subset_1(F_118, k1_zfmisc_1(k2_zfmisc_1(C_121, D_117))) | ~v1_funct_1(F_118) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_116, B_120))) | ~v1_funct_1(E_119))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.89/1.93  tff(c_714, plain, (![A_116, B_120, E_119]: (k1_partfun1(A_116, B_120, '#skF_2', '#skF_1', E_119, '#skF_4')=k5_relat_1(E_119, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_116, B_120))) | ~v1_funct_1(E_119))), inference(resolution, [status(thm)], [c_74, c_704])).
% 4.89/1.93  tff(c_849, plain, (![A_134, B_135, E_136]: (k1_partfun1(A_134, B_135, '#skF_2', '#skF_1', E_136, '#skF_4')=k5_relat_1(E_136, '#skF_4') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(E_136))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_714])).
% 4.89/1.93  tff(c_861, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_849])).
% 4.89/1.93  tff(c_872, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_861])).
% 4.89/1.93  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.89/1.93  tff(c_559, plain, (![D_98, C_99, A_100, B_101]: (D_98=C_99 | ~r2_relset_1(A_100, B_101, C_99, D_98) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.89/1.93  tff(c_571, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_559])).
% 4.89/1.93  tff(c_592, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_571])).
% 4.89/1.93  tff(c_593, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_592])).
% 4.89/1.93  tff(c_877, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_872, c_593])).
% 4.89/1.93  tff(c_976, plain, (![C_144, B_147, D_145, F_143, A_148, E_146]: (m1_subset_1(k1_partfun1(A_148, B_147, C_144, D_145, E_146, F_143), k1_zfmisc_1(k2_zfmisc_1(A_148, D_145))) | ~m1_subset_1(F_143, k1_zfmisc_1(k2_zfmisc_1(C_144, D_145))) | ~v1_funct_1(F_143) | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))) | ~v1_funct_1(E_146))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.89/1.93  tff(c_1040, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_872, c_976])).
% 4.89/1.93  tff(c_1068, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_1040])).
% 4.89/1.93  tff(c_1070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_877, c_1068])).
% 4.89/1.93  tff(c_1071, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_592])).
% 4.89/1.93  tff(c_2126, plain, (![A_207, B_208, C_209, D_210]: (k2_relset_1(A_207, B_208, C_209)=B_208 | ~r2_relset_1(B_208, B_208, k1_partfun1(B_208, A_207, A_207, B_208, D_210, C_209), k6_partfun1(B_208)) | ~m1_subset_1(D_210, k1_zfmisc_1(k2_zfmisc_1(B_208, A_207))) | ~v1_funct_2(D_210, B_208, A_207) | ~v1_funct_1(D_210) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_2(C_209, A_207, B_208) | ~v1_funct_1(C_209))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.89/1.93  tff(c_2132, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1071, c_2126])).
% 4.89/1.93  tff(c_2136, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_84, c_82, c_80, c_163, c_217, c_2132])).
% 4.89/1.93  tff(c_2138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1112, c_2136])).
% 4.89/1.93  tff(c_2139, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1107])).
% 4.89/1.93  tff(c_2140, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_1107])).
% 4.89/1.93  tff(c_254, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_237])).
% 4.89/1.93  tff(c_398, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_383])).
% 4.89/1.93  tff(c_412, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_254, c_398])).
% 4.89/1.93  tff(c_413, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_66, c_412])).
% 4.89/1.93  tff(c_56, plain, (![A_49]: (m1_subset_1(A_49, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_49), k2_relat_1(A_49)))) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.89/1.93  tff(c_212, plain, (![A_49]: (k2_relset_1(k1_relat_1(A_49), k2_relat_1(A_49), A_49)=k2_relat_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_56, c_199])).
% 4.89/1.93  tff(c_457, plain, (k2_relset_1('#skF_2', k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_413, c_212])).
% 4.89/1.93  tff(c_473, plain, (k2_relset_1('#skF_2', k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_78, c_457])).
% 4.89/1.93  tff(c_2141, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2140, c_2140, c_473])).
% 4.89/1.93  tff(c_85, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_partfun1(k2_relat_1(A_11))!=k5_relat_1(B_13, A_11) | k2_relat_1(B_13)!=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 4.89/1.93  tff(c_2153, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2140, c_85])).
% 4.89/1.93  tff(c_2172, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_78, c_413, c_2153])).
% 4.89/1.93  tff(c_2192, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2172])).
% 4.89/1.93  tff(c_14, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.89/1.93  tff(c_86, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 4.89/1.93  tff(c_2288, plain, (![D_227, C_231, F_228, E_229, A_226, B_230]: (k1_partfun1(A_226, B_230, C_231, D_227, E_229, F_228)=k5_relat_1(E_229, F_228) | ~m1_subset_1(F_228, k1_zfmisc_1(k2_zfmisc_1(C_231, D_227))) | ~v1_funct_1(F_228) | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_226, B_230))) | ~v1_funct_1(E_229))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.89/1.93  tff(c_2296, plain, (![A_226, B_230, E_229]: (k1_partfun1(A_226, B_230, '#skF_2', '#skF_1', E_229, '#skF_4')=k5_relat_1(E_229, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_226, B_230))) | ~v1_funct_1(E_229))), inference(resolution, [status(thm)], [c_74, c_2288])).
% 4.89/1.93  tff(c_2307, plain, (![A_233, B_234, E_235]: (k1_partfun1(A_233, B_234, '#skF_2', '#skF_1', E_235, '#skF_4')=k5_relat_1(E_235, '#skF_4') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_235))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2296])).
% 4.89/1.93  tff(c_2316, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_2307])).
% 4.89/1.93  tff(c_2324, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1071, c_2316])).
% 4.89/1.93  tff(c_10, plain, (![A_7, B_9]: (v2_funct_1(A_7) | k2_relat_1(B_9)!=k1_relat_1(A_7) | ~v2_funct_1(k5_relat_1(B_9, A_7)) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.89/1.93  tff(c_2331, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2324, c_10])).
% 4.89/1.93  tff(c_2338, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_78, c_139, c_84, c_86, c_216, c_413, c_2331])).
% 4.89/1.93  tff(c_2340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2192, c_2338])).
% 4.89/1.93  tff(c_2342, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2172])).
% 4.89/1.93  tff(c_2343, plain, (![B_236]: (k2_funct_1('#skF_4')=B_236 | k5_relat_1(B_236, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_236)!='#skF_2' | ~v1_funct_1(B_236) | ~v1_relat_1(B_236))), inference(splitRight, [status(thm)], [c_2172])).
% 4.89/1.93  tff(c_2352, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_139, c_2343])).
% 4.89/1.93  tff(c_2363, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_216, c_2352])).
% 4.89/1.93  tff(c_2365, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_2363])).
% 4.89/1.93  tff(c_2467, plain, (![D_253, A_252, E_255, B_256, F_254, C_257]: (k1_partfun1(A_252, B_256, C_257, D_253, E_255, F_254)=k5_relat_1(E_255, F_254) | ~m1_subset_1(F_254, k1_zfmisc_1(k2_zfmisc_1(C_257, D_253))) | ~v1_funct_1(F_254) | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(A_252, B_256))) | ~v1_funct_1(E_255))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.89/1.93  tff(c_2475, plain, (![A_252, B_256, E_255]: (k1_partfun1(A_252, B_256, '#skF_2', '#skF_1', E_255, '#skF_4')=k5_relat_1(E_255, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(A_252, B_256))) | ~v1_funct_1(E_255))), inference(resolution, [status(thm)], [c_74, c_2467])).
% 4.89/1.93  tff(c_2486, plain, (![A_259, B_260, E_261]: (k1_partfun1(A_259, B_260, '#skF_2', '#skF_1', E_261, '#skF_4')=k5_relat_1(E_261, '#skF_4') | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))) | ~v1_funct_1(E_261))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2475])).
% 4.89/1.93  tff(c_2495, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_2486])).
% 4.89/1.93  tff(c_2503, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1071, c_2495])).
% 4.89/1.93  tff(c_2505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2365, c_2503])).
% 4.89/1.93  tff(c_2506, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_2363])).
% 4.89/1.93  tff(c_2737, plain, (![A_290, C_291, B_292]: (k6_partfun1(A_290)=k5_relat_1(C_291, k2_funct_1(C_291)) | k1_xboole_0=B_292 | ~v2_funct_1(C_291) | k2_relset_1(A_290, B_292, C_291)!=B_292 | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_290, B_292))) | ~v1_funct_2(C_291, A_290, B_292) | ~v1_funct_1(C_291))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.89/1.93  tff(c_2745, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_2737])).
% 4.89/1.93  tff(c_2756, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2141, c_2342, c_2506, c_2745])).
% 4.89/1.93  tff(c_2758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_2139, c_2756])).
% 4.89/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.93  
% 4.89/1.93  Inference rules
% 4.89/1.93  ----------------------
% 4.89/1.93  #Ref     : 0
% 4.89/1.93  #Sup     : 560
% 4.89/1.93  #Fact    : 0
% 4.89/1.93  #Define  : 0
% 4.89/1.93  #Split   : 19
% 4.89/1.93  #Chain   : 0
% 4.89/1.93  #Close   : 0
% 4.89/1.93  
% 4.89/1.93  Ordering : KBO
% 4.89/1.93  
% 4.89/1.93  Simplification rules
% 4.89/1.93  ----------------------
% 4.89/1.93  #Subsume      : 27
% 4.89/1.93  #Demod        : 795
% 4.89/1.93  #Tautology    : 210
% 4.89/1.93  #SimpNegUnit  : 36
% 4.89/1.93  #BackRed      : 39
% 4.89/1.93  
% 4.89/1.93  #Partial instantiations: 0
% 4.89/1.93  #Strategies tried      : 1
% 4.89/1.93  
% 4.89/1.93  Timing (in seconds)
% 4.89/1.93  ----------------------
% 4.89/1.93  Preprocessing        : 0.39
% 4.89/1.93  Parsing              : 0.21
% 4.89/1.93  CNF conversion       : 0.03
% 4.89/1.93  Main loop            : 0.77
% 4.89/1.93  Inferencing          : 0.25
% 4.89/1.93  Reduction            : 0.30
% 4.89/1.93  Demodulation         : 0.22
% 4.89/1.93  BG Simplification    : 0.04
% 4.89/1.93  Subsumption          : 0.12
% 4.89/1.93  Abstraction          : 0.04
% 4.89/1.93  MUC search           : 0.00
% 4.89/1.93  Cooper               : 0.00
% 4.89/1.93  Total                : 1.20
% 4.89/1.93  Index Insertion      : 0.00
% 4.89/1.93  Index Deletion       : 0.00
% 4.89/1.93  Index Matching       : 0.00
% 4.89/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
