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
% DateTime   : Thu Dec  3 10:15:55 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :  196 (1730 expanded)
%              Number of leaves         :   46 ( 581 expanded)
%              Depth                    :   16
%              Number of atoms          :  363 (4433 expanded)
%              Number of equality atoms :  128 (1497 expanded)
%              Maximal formula depth    :   17 (   3 average)
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

tff(f_191,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_125,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_169,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_42,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_67,axiom,(
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

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_820,plain,(
    ! [A_113,B_114,D_115] :
      ( r2_relset_1(A_113,B_114,D_115,D_115)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_831,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_820])).

tff(c_52,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6,plain,(
    ! [A_2] : k1_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [A_2] : k1_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6])).

tff(c_18,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    ! [A_5] : v1_relat_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_160,plain,(
    ! [A_50] :
      ( k1_relat_1(A_50) != k1_xboole_0
      | k1_xboole_0 = A_50
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_166,plain,(
    ! [A_5] :
      ( k1_relat_1(k6_partfun1(A_5)) != k1_xboole_0
      | k6_partfun1(A_5) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_81,c_160])).

tff(c_172,plain,(
    ! [A_5] :
      ( k1_xboole_0 != A_5
      | k6_partfun1(A_5) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_166])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_209,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_62])).

tff(c_288,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_78,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_76,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_72,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_226,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_244,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_226])).

tff(c_291,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_307,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_291])).

tff(c_392,plain,(
    ! [B_73,A_74] :
      ( k2_relat_1(B_73) = A_74
      | ~ v2_funct_2(B_73,A_74)
      | ~ v5_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_401,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_307,c_392])).

tff(c_413,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_401])).

tff(c_645,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_74,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_743,plain,(
    ! [C_109,B_110,A_111] :
      ( v2_funct_2(C_109,B_110)
      | ~ v3_funct_2(C_109,A_111,B_110)
      | ~ v1_funct_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_755,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_743])).

tff(c_767,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_755])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_645,c_767])).

tff(c_770,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_840,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_852,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_840])).

tff(c_860,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_852])).

tff(c_893,plain,(
    ! [C_123,A_124,B_125] :
      ( v2_funct_1(C_123)
      | ~ v3_funct_2(C_123,A_124,B_125)
      | ~ v1_funct_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_905,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_893])).

tff(c_917,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_905])).

tff(c_1550,plain,(
    ! [C_165,D_166,B_167,A_168] :
      ( k2_funct_1(C_165) = D_166
      | k1_xboole_0 = B_167
      | k1_xboole_0 = A_168
      | ~ v2_funct_1(C_165)
      | ~ r2_relset_1(A_168,A_168,k1_partfun1(A_168,B_167,B_167,A_168,C_165,D_166),k6_partfun1(A_168))
      | k2_relset_1(A_168,B_167,C_165) != B_167
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(B_167,A_168)))
      | ~ v1_funct_2(D_166,B_167,A_168)
      | ~ v1_funct_1(D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167)))
      | ~ v1_funct_2(C_165,A_168,B_167)
      | ~ v1_funct_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1553,plain,
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
    inference(resolution,[status(thm)],[c_62,c_1550])).

tff(c_1559,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_68,c_64,c_860,c_917,c_1553])).

tff(c_1560,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_1559])).

tff(c_1042,plain,(
    ! [A_138,B_139] :
      ( k2_funct_2(A_138,B_139) = k2_funct_1(B_139)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(A_138,A_138)))
      | ~ v3_funct_2(B_139,A_138,A_138)
      | ~ v1_funct_2(B_139,A_138,A_138)
      | ~ v1_funct_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1054,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1042])).

tff(c_1066,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1054])).

tff(c_60,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1071,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_60])).

tff(c_1561,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_1071])).

tff(c_1565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_1561])).

tff(c_1567,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_243,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_226])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_251,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_243,c_2])).

tff(c_287,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_1568,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_287])).

tff(c_1610,plain,(
    ! [C_169,B_170,A_171] :
      ( v5_relat_1(C_169,B_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_171,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1621,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_1610])).

tff(c_1763,plain,(
    ! [B_184,A_185] :
      ( k2_relat_1(B_184) = A_185
      | ~ v2_funct_2(B_184,A_185)
      | ~ v5_relat_1(B_184,A_185)
      | ~ v1_relat_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1775,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1621,c_1763])).

tff(c_1788,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_1775])).

tff(c_1789,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1568,c_1788])).

tff(c_66,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1993,plain,(
    ! [C_204,B_205,A_206] :
      ( v2_funct_2(C_204,B_205)
      | ~ v3_funct_2(C_204,A_206,B_205)
      | ~ v1_funct_1(C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2002,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1993])).

tff(c_2014,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2002])).

tff(c_2016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1789,c_2014])).

tff(c_2017,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_2075,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_3')
    | '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2017,c_2017,c_209])).

tff(c_2076,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2075])).

tff(c_2018,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_2047,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2017,c_2018])).

tff(c_2061,plain,(
    ! [C_207,B_208,A_209] :
      ( v5_relat_1(C_207,B_208)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_209,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2072,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_2061])).

tff(c_2204,plain,(
    ! [B_220,A_221] :
      ( k2_relat_1(B_220) = A_221
      | ~ v2_funct_2(B_220,A_221)
      | ~ v5_relat_1(B_220,A_221)
      | ~ v1_relat_1(B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2216,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2072,c_2204])).

tff(c_2228,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_2047,c_2216])).

tff(c_2229,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2076,c_2228])).

tff(c_2427,plain,(
    ! [C_239,B_240,A_241] :
      ( v2_funct_2(C_239,B_240)
      | ~ v3_funct_2(C_239,A_241,B_240)
      | ~ v1_funct_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_241,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2436,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2427])).

tff(c_2448,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2436])).

tff(c_2450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2229,c_2448])).

tff(c_2452,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2075])).

tff(c_2458,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_2017])).

tff(c_175,plain,(
    ! [A_51] :
      ( k1_xboole_0 != A_51
      | k6_partfun1(A_51) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_166])).

tff(c_48,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_181,plain,(
    ! [A_51] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_51,A_51)))
      | k1_xboole_0 != A_51 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_48])).

tff(c_3114,plain,(
    ! [A_295] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_295,A_295)))
      | A_295 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2458,c_2458,c_181])).

tff(c_32,plain,(
    ! [A_18,B_19,D_21] :
      ( r2_relset_1(A_18,B_19,D_21,D_21)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3131,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3114,c_32])).

tff(c_2465,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_70])).

tff(c_2455,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_2452,c_2047])).

tff(c_95,plain,(
    ! [A_46] : k6_relat_1(A_46) = k6_partfun1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_101,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_12])).

tff(c_117,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_81])).

tff(c_173,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_166])).

tff(c_8,plain,(
    ! [A_2] : k2_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [A_47] : k2_relat_1(k6_partfun1(A_47)) = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_133,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_124])).

tff(c_10,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k6_relat_1(k2_relat_1(A_3))) = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_261,plain,(
    ! [A_57] :
      ( k5_relat_1(A_57,k6_partfun1(k2_relat_1(A_57))) = A_57
      | ~ v1_relat_1(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10])).

tff(c_273,plain,
    ( k5_relat_1(k1_xboole_0,k6_partfun1(k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_261])).

tff(c_280,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_173,c_273])).

tff(c_2019,plain,(
    k5_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2017,c_2017,c_2017,c_280])).

tff(c_2557,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_2452,c_2452,c_2019])).

tff(c_2459,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_243])).

tff(c_20,plain,(
    ! [A_5] : v2_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    ! [A_5] : v2_funct_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_119,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_80])).

tff(c_2028,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2017,c_119])).

tff(c_2457,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_2028])).

tff(c_140,plain,(
    ! [A_48] : k1_relat_1(k6_partfun1(A_48)) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6])).

tff(c_149,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_140])).

tff(c_2025,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2017,c_2017,c_149])).

tff(c_2454,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_2452,c_2025])).

tff(c_2022,plain,(
    ! [A_5] :
      ( A_5 != '#skF_3'
      | k6_partfun1(A_5) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2017,c_2017,c_172])).

tff(c_2946,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_2452,c_2022])).

tff(c_22,plain,(
    ! [A_6,B_8] :
      ( k2_funct_1(A_6) = B_8
      | k6_relat_1(k2_relat_1(A_6)) != k5_relat_1(B_8,A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3326,plain,(
    ! [A_321,B_322] :
      ( k2_funct_1(A_321) = B_322
      | k6_partfun1(k2_relat_1(A_321)) != k5_relat_1(B_322,A_321)
      | k2_relat_1(B_322) != k1_relat_1(A_321)
      | ~ v2_funct_1(A_321)
      | ~ v1_funct_1(B_322)
      | ~ v1_relat_1(B_322)
      | ~ v1_funct_1(A_321)
      | ~ v1_relat_1(A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_22])).

tff(c_3335,plain,(
    ! [B_322] :
      ( k2_funct_1('#skF_1') = B_322
      | k5_relat_1(B_322,'#skF_1') != k6_partfun1('#skF_1')
      | k2_relat_1(B_322) != k1_relat_1('#skF_1')
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1(B_322)
      | ~ v1_relat_1(B_322)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2455,c_3326])).

tff(c_3515,plain,(
    ! [B_330] :
      ( k2_funct_1('#skF_1') = B_330
      | k5_relat_1(B_330,'#skF_1') != '#skF_1'
      | k2_relat_1(B_330) != '#skF_1'
      | ~ v1_funct_1(B_330)
      | ~ v1_relat_1(B_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2459,c_2465,c_2457,c_2454,c_2946,c_3335])).

tff(c_3521,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != '#skF_1'
    | k2_relat_1('#skF_1') != '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2459,c_3515])).

tff(c_3531,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2465,c_2455,c_2557,c_3521])).

tff(c_2463,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_68])).

tff(c_2464,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_66])).

tff(c_3111,plain,(
    ! [A_51] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_51,A_51)))
      | A_51 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2458,c_2458,c_181])).

tff(c_3300,plain,(
    ! [A_318,B_319] :
      ( k2_funct_2(A_318,B_319) = k2_funct_1(B_319)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(k2_zfmisc_1(A_318,A_318)))
      | ~ v3_funct_2(B_319,A_318,A_318)
      | ~ v1_funct_2(B_319,A_318,A_318)
      | ~ v1_funct_1(B_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3303,plain,(
    ! [A_51] :
      ( k2_funct_2(A_51,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_51,A_51)
      | ~ v1_funct_2('#skF_1',A_51,A_51)
      | ~ v1_funct_1('#skF_1')
      | A_51 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3111,c_3300])).

tff(c_3314,plain,(
    ! [A_320] :
      ( k2_funct_2(A_320,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_320,A_320)
      | ~ v1_funct_2('#skF_1',A_320,A_320)
      | A_320 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2465,c_3303])).

tff(c_3317,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2464,c_3314])).

tff(c_3320,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2463,c_3317])).

tff(c_259,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_2562,plain,
    ( k2_relat_1('#skF_2') != '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2458,c_2458,c_259])).

tff(c_2563,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2562])).

tff(c_2073,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_2061])).

tff(c_2642,plain,(
    ! [B_253,A_254] :
      ( k2_relat_1(B_253) = A_254
      | ~ v2_funct_2(B_253,A_254)
      | ~ v5_relat_1(B_253,A_254)
      | ~ v1_relat_1(B_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2651,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2073,c_2642])).

tff(c_2660,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_2651])).

tff(c_2661,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2563,c_2660])).

tff(c_2904,plain,(
    ! [C_277,B_278,A_279] :
      ( v2_funct_2(C_277,B_278)
      | ~ v3_funct_2(C_277,A_279,B_278)
      | ~ v1_funct_1(C_277)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_279,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2913,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_2904])).

tff(c_2922,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_2913])).

tff(c_2924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2661,c_2922])).

tff(c_2925,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2562])).

tff(c_2461,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_60])).

tff(c_3100,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2925,c_2461])).

tff(c_3321,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3320,c_3100])).

tff(c_3540,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3531,c_3321])).

tff(c_3548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_3540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n007.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 10:19:06 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.52/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.27  
% 5.52/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.27  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.52/2.27  
% 5.52/2.27  %Foreground sorts:
% 5.52/2.27  
% 5.52/2.27  
% 5.52/2.27  %Background operators:
% 5.52/2.27  
% 5.52/2.27  
% 5.52/2.27  %Foreground operators:
% 5.52/2.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.52/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.52/2.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.52/2.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.52/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.52/2.27  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.52/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.52/2.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.52/2.27  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.52/2.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.52/2.27  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.52/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.52/2.27  tff('#skF_2', type, '#skF_2': $i).
% 5.52/2.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.52/2.27  tff('#skF_3', type, '#skF_3': $i).
% 5.52/2.27  tff('#skF_1', type, '#skF_1': $i).
% 5.52/2.27  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.52/2.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.52/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.52/2.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.52/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.52/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.52/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.52/2.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.52/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.52/2.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.52/2.27  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.52/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.52/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.52/2.27  
% 5.79/2.30  tff(f_191, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 5.79/2.30  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.79/2.30  tff(f_125, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.79/2.30  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.79/2.30  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.79/2.30  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.79/2.30  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.79/2.30  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.79/2.30  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.79/2.30  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.79/2.30  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.79/2.30  tff(f_169, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 5.79/2.30  tff(f_123, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.79/2.30  tff(f_113, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.79/2.30  tff(f_42, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 5.79/2.30  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 5.79/2.30  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 5.79/2.30  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.79/2.30  tff(c_820, plain, (![A_113, B_114, D_115]: (r2_relset_1(A_113, B_114, D_115, D_115) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.79/2.30  tff(c_831, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_820])).
% 5.79/2.30  tff(c_52, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.79/2.30  tff(c_6, plain, (![A_2]: (k1_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.79/2.30  tff(c_86, plain, (![A_2]: (k1_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6])).
% 5.79/2.30  tff(c_18, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.79/2.30  tff(c_81, plain, (![A_5]: (v1_relat_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 5.79/2.30  tff(c_160, plain, (![A_50]: (k1_relat_1(A_50)!=k1_xboole_0 | k1_xboole_0=A_50 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.79/2.30  tff(c_166, plain, (![A_5]: (k1_relat_1(k6_partfun1(A_5))!=k1_xboole_0 | k6_partfun1(A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_81, c_160])).
% 5.79/2.30  tff(c_172, plain, (![A_5]: (k1_xboole_0!=A_5 | k6_partfun1(A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_166])).
% 5.79/2.30  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.79/2.30  tff(c_209, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_172, c_62])).
% 5.79/2.30  tff(c_288, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_209])).
% 5.79/2.30  tff(c_78, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.79/2.30  tff(c_76, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.79/2.30  tff(c_72, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.79/2.30  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.79/2.30  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.79/2.30  tff(c_226, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.79/2.30  tff(c_244, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_226])).
% 5.79/2.30  tff(c_291, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.79/2.30  tff(c_307, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_291])).
% 5.79/2.30  tff(c_392, plain, (![B_73, A_74]: (k2_relat_1(B_73)=A_74 | ~v2_funct_2(B_73, A_74) | ~v5_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.79/2.30  tff(c_401, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_307, c_392])).
% 5.79/2.30  tff(c_413, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_401])).
% 5.79/2.30  tff(c_645, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_413])).
% 5.79/2.30  tff(c_74, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.79/2.30  tff(c_743, plain, (![C_109, B_110, A_111]: (v2_funct_2(C_109, B_110) | ~v3_funct_2(C_109, A_111, B_110) | ~v1_funct_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.79/2.30  tff(c_755, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_743])).
% 5.79/2.30  tff(c_767, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_755])).
% 5.79/2.30  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_645, c_767])).
% 5.79/2.30  tff(c_770, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_413])).
% 5.79/2.30  tff(c_840, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.79/2.30  tff(c_852, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_840])).
% 5.79/2.30  tff(c_860, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_770, c_852])).
% 5.79/2.30  tff(c_893, plain, (![C_123, A_124, B_125]: (v2_funct_1(C_123) | ~v3_funct_2(C_123, A_124, B_125) | ~v1_funct_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.79/2.30  tff(c_905, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_893])).
% 5.79/2.30  tff(c_917, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_905])).
% 5.79/2.30  tff(c_1550, plain, (![C_165, D_166, B_167, A_168]: (k2_funct_1(C_165)=D_166 | k1_xboole_0=B_167 | k1_xboole_0=A_168 | ~v2_funct_1(C_165) | ~r2_relset_1(A_168, A_168, k1_partfun1(A_168, B_167, B_167, A_168, C_165, D_166), k6_partfun1(A_168)) | k2_relset_1(A_168, B_167, C_165)!=B_167 | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(B_167, A_168))) | ~v1_funct_2(D_166, B_167, A_168) | ~v1_funct_1(D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))) | ~v1_funct_2(C_165, A_168, B_167) | ~v1_funct_1(C_165))), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.79/2.30  tff(c_1553, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_1550])).
% 5.79/2.30  tff(c_1559, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_68, c_64, c_860, c_917, c_1553])).
% 5.79/2.30  tff(c_1560, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_288, c_1559])).
% 5.79/2.30  tff(c_1042, plain, (![A_138, B_139]: (k2_funct_2(A_138, B_139)=k2_funct_1(B_139) | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(A_138, A_138))) | ~v3_funct_2(B_139, A_138, A_138) | ~v1_funct_2(B_139, A_138, A_138) | ~v1_funct_1(B_139))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.79/2.30  tff(c_1054, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_1042])).
% 5.79/2.30  tff(c_1066, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1054])).
% 5.79/2.30  tff(c_60, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.79/2.30  tff(c_1071, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_60])).
% 5.79/2.30  tff(c_1561, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1560, c_1071])).
% 5.79/2.30  tff(c_1565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_831, c_1561])).
% 5.79/2.30  tff(c_1567, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_209])).
% 5.79/2.30  tff(c_243, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_226])).
% 5.79/2.30  tff(c_2, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.79/2.30  tff(c_251, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_243, c_2])).
% 5.79/2.30  tff(c_287, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_251])).
% 5.79/2.30  tff(c_1568, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1567, c_287])).
% 5.79/2.30  tff(c_1610, plain, (![C_169, B_170, A_171]: (v5_relat_1(C_169, B_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_171, B_170))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.79/2.30  tff(c_1621, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_1610])).
% 5.79/2.30  tff(c_1763, plain, (![B_184, A_185]: (k2_relat_1(B_184)=A_185 | ~v2_funct_2(B_184, A_185) | ~v5_relat_1(B_184, A_185) | ~v1_relat_1(B_184))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.79/2.30  tff(c_1775, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1621, c_1763])).
% 5.79/2.30  tff(c_1788, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_1775])).
% 5.79/2.30  tff(c_1789, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1568, c_1788])).
% 5.79/2.30  tff(c_66, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.79/2.30  tff(c_1993, plain, (![C_204, B_205, A_206]: (v2_funct_2(C_204, B_205) | ~v3_funct_2(C_204, A_206, B_205) | ~v1_funct_1(C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.79/2.30  tff(c_2002, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1993])).
% 5.79/2.30  tff(c_2014, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2002])).
% 5.79/2.30  tff(c_2016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1789, c_2014])).
% 5.79/2.30  tff(c_2017, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_251])).
% 5.79/2.30  tff(c_2075, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_3') | '#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2017, c_2017, c_209])).
% 5.79/2.30  tff(c_2076, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_2075])).
% 5.79/2.30  tff(c_2018, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_251])).
% 5.79/2.30  tff(c_2047, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2017, c_2018])).
% 5.79/2.30  tff(c_2061, plain, (![C_207, B_208, A_209]: (v5_relat_1(C_207, B_208) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_209, B_208))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.79/2.30  tff(c_2072, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_2061])).
% 5.79/2.30  tff(c_2204, plain, (![B_220, A_221]: (k2_relat_1(B_220)=A_221 | ~v2_funct_2(B_220, A_221) | ~v5_relat_1(B_220, A_221) | ~v1_relat_1(B_220))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.79/2.30  tff(c_2216, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2072, c_2204])).
% 5.79/2.30  tff(c_2228, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_2047, c_2216])).
% 5.79/2.30  tff(c_2229, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2076, c_2228])).
% 5.79/2.30  tff(c_2427, plain, (![C_239, B_240, A_241]: (v2_funct_2(C_239, B_240) | ~v3_funct_2(C_239, A_241, B_240) | ~v1_funct_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_241, B_240))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.79/2.30  tff(c_2436, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2427])).
% 5.79/2.30  tff(c_2448, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2436])).
% 5.79/2.30  tff(c_2450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2229, c_2448])).
% 5.79/2.30  tff(c_2452, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2075])).
% 5.79/2.30  tff(c_2458, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_2017])).
% 5.79/2.30  tff(c_175, plain, (![A_51]: (k1_xboole_0!=A_51 | k6_partfun1(A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_166])).
% 5.79/2.30  tff(c_48, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.79/2.30  tff(c_181, plain, (![A_51]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_51, A_51))) | k1_xboole_0!=A_51)), inference(superposition, [status(thm), theory('equality')], [c_175, c_48])).
% 5.79/2.30  tff(c_3114, plain, (![A_295]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_295, A_295))) | A_295!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2458, c_2458, c_181])).
% 5.79/2.30  tff(c_32, plain, (![A_18, B_19, D_21]: (r2_relset_1(A_18, B_19, D_21, D_21) | ~m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.79/2.30  tff(c_3131, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3114, c_32])).
% 5.79/2.30  tff(c_2465, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_70])).
% 5.79/2.30  tff(c_2455, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_2452, c_2047])).
% 5.79/2.30  tff(c_95, plain, (![A_46]: (k6_relat_1(A_46)=k6_partfun1(A_46))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.79/2.30  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.79/2.30  tff(c_101, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_95, c_12])).
% 5.79/2.30  tff(c_117, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_81])).
% 5.79/2.30  tff(c_173, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_166])).
% 5.79/2.30  tff(c_8, plain, (![A_2]: (k2_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.79/2.30  tff(c_124, plain, (![A_47]: (k2_relat_1(k6_partfun1(A_47))=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8])).
% 5.79/2.30  tff(c_133, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_101, c_124])).
% 5.79/2.30  tff(c_10, plain, (![A_3]: (k5_relat_1(A_3, k6_relat_1(k2_relat_1(A_3)))=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.79/2.30  tff(c_261, plain, (![A_57]: (k5_relat_1(A_57, k6_partfun1(k2_relat_1(A_57)))=A_57 | ~v1_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10])).
% 5.79/2.30  tff(c_273, plain, (k5_relat_1(k1_xboole_0, k6_partfun1(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_133, c_261])).
% 5.79/2.30  tff(c_280, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_117, c_173, c_273])).
% 5.79/2.30  tff(c_2019, plain, (k5_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2017, c_2017, c_2017, c_280])).
% 5.79/2.30  tff(c_2557, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_2452, c_2452, c_2019])).
% 5.79/2.30  tff(c_2459, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_243])).
% 5.79/2.30  tff(c_20, plain, (![A_5]: (v2_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.79/2.30  tff(c_80, plain, (![A_5]: (v2_funct_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20])).
% 5.79/2.30  tff(c_119, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_80])).
% 5.79/2.30  tff(c_2028, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2017, c_119])).
% 5.79/2.30  tff(c_2457, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_2028])).
% 5.79/2.30  tff(c_140, plain, (![A_48]: (k1_relat_1(k6_partfun1(A_48))=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6])).
% 5.79/2.30  tff(c_149, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_101, c_140])).
% 5.79/2.30  tff(c_2025, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2017, c_2017, c_149])).
% 5.79/2.30  tff(c_2454, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_2452, c_2025])).
% 5.79/2.30  tff(c_2022, plain, (![A_5]: (A_5!='#skF_3' | k6_partfun1(A_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2017, c_2017, c_172])).
% 5.79/2.30  tff(c_2946, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_2452, c_2022])).
% 5.79/2.30  tff(c_22, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_relat_1(k2_relat_1(A_6))!=k5_relat_1(B_8, A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.79/2.30  tff(c_3326, plain, (![A_321, B_322]: (k2_funct_1(A_321)=B_322 | k6_partfun1(k2_relat_1(A_321))!=k5_relat_1(B_322, A_321) | k2_relat_1(B_322)!=k1_relat_1(A_321) | ~v2_funct_1(A_321) | ~v1_funct_1(B_322) | ~v1_relat_1(B_322) | ~v1_funct_1(A_321) | ~v1_relat_1(A_321))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_22])).
% 5.79/2.30  tff(c_3335, plain, (![B_322]: (k2_funct_1('#skF_1')=B_322 | k5_relat_1(B_322, '#skF_1')!=k6_partfun1('#skF_1') | k2_relat_1(B_322)!=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1(B_322) | ~v1_relat_1(B_322) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2455, c_3326])).
% 5.79/2.30  tff(c_3515, plain, (![B_330]: (k2_funct_1('#skF_1')=B_330 | k5_relat_1(B_330, '#skF_1')!='#skF_1' | k2_relat_1(B_330)!='#skF_1' | ~v1_funct_1(B_330) | ~v1_relat_1(B_330))), inference(demodulation, [status(thm), theory('equality')], [c_2459, c_2465, c_2457, c_2454, c_2946, c_3335])).
% 5.79/2.30  tff(c_3521, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!='#skF_1' | k2_relat_1('#skF_1')!='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2459, c_3515])).
% 5.79/2.30  tff(c_3531, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2465, c_2455, c_2557, c_3521])).
% 5.79/2.30  tff(c_2463, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_68])).
% 5.79/2.30  tff(c_2464, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_66])).
% 5.79/2.30  tff(c_3111, plain, (![A_51]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_51, A_51))) | A_51!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2458, c_2458, c_181])).
% 5.79/2.30  tff(c_3300, plain, (![A_318, B_319]: (k2_funct_2(A_318, B_319)=k2_funct_1(B_319) | ~m1_subset_1(B_319, k1_zfmisc_1(k2_zfmisc_1(A_318, A_318))) | ~v3_funct_2(B_319, A_318, A_318) | ~v1_funct_2(B_319, A_318, A_318) | ~v1_funct_1(B_319))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.79/2.30  tff(c_3303, plain, (![A_51]: (k2_funct_2(A_51, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_51, A_51) | ~v1_funct_2('#skF_1', A_51, A_51) | ~v1_funct_1('#skF_1') | A_51!='#skF_1')), inference(resolution, [status(thm)], [c_3111, c_3300])).
% 5.79/2.30  tff(c_3314, plain, (![A_320]: (k2_funct_2(A_320, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_320, A_320) | ~v1_funct_2('#skF_1', A_320, A_320) | A_320!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2465, c_3303])).
% 5.79/2.30  tff(c_3317, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2464, c_3314])).
% 5.79/2.30  tff(c_3320, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2463, c_3317])).
% 5.79/2.30  tff(c_259, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_244, c_2])).
% 5.79/2.30  tff(c_2562, plain, (k2_relat_1('#skF_2')!='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2458, c_2458, c_259])).
% 5.79/2.30  tff(c_2563, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2562])).
% 5.79/2.30  tff(c_2073, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_2061])).
% 5.79/2.30  tff(c_2642, plain, (![B_253, A_254]: (k2_relat_1(B_253)=A_254 | ~v2_funct_2(B_253, A_254) | ~v5_relat_1(B_253, A_254) | ~v1_relat_1(B_253))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.79/2.30  tff(c_2651, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2073, c_2642])).
% 5.79/2.30  tff(c_2660, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_2651])).
% 5.79/2.30  tff(c_2661, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2563, c_2660])).
% 5.79/2.30  tff(c_2904, plain, (![C_277, B_278, A_279]: (v2_funct_2(C_277, B_278) | ~v3_funct_2(C_277, A_279, B_278) | ~v1_funct_1(C_277) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_279, B_278))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.79/2.30  tff(c_2913, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_2904])).
% 5.79/2.30  tff(c_2922, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_2913])).
% 5.79/2.30  tff(c_2924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2661, c_2922])).
% 5.79/2.30  tff(c_2925, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_2562])).
% 5.79/2.30  tff(c_2461, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_60])).
% 5.79/2.30  tff(c_3100, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2925, c_2461])).
% 5.79/2.30  tff(c_3321, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3320, c_3100])).
% 5.79/2.30  tff(c_3540, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3531, c_3321])).
% 5.79/2.30  tff(c_3548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3131, c_3540])).
% 5.79/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.79/2.30  
% 5.79/2.30  Inference rules
% 5.79/2.30  ----------------------
% 5.79/2.30  #Ref     : 3
% 5.79/2.30  #Sup     : 739
% 5.79/2.30  #Fact    : 0
% 5.79/2.30  #Define  : 0
% 5.79/2.30  #Split   : 27
% 5.79/2.30  #Chain   : 0
% 5.79/2.30  #Close   : 0
% 5.79/2.30  
% 5.79/2.30  Ordering : KBO
% 5.79/2.30  
% 5.79/2.30  Simplification rules
% 5.79/2.30  ----------------------
% 5.79/2.30  #Subsume      : 208
% 5.79/2.30  #Demod        : 829
% 5.79/2.30  #Tautology    : 420
% 5.79/2.30  #SimpNegUnit  : 69
% 5.79/2.30  #BackRed      : 108
% 5.79/2.30  
% 5.79/2.30  #Partial instantiations: 0
% 5.79/2.30  #Strategies tried      : 1
% 5.79/2.30  
% 5.79/2.30  Timing (in seconds)
% 5.79/2.30  ----------------------
% 5.79/2.30  Preprocessing        : 0.56
% 5.79/2.30  Parsing              : 0.31
% 5.79/2.30  CNF conversion       : 0.04
% 5.79/2.30  Main loop            : 0.78
% 5.79/2.30  Inferencing          : 0.27
% 5.79/2.30  Reduction            : 0.30
% 5.79/2.30  Demodulation         : 0.21
% 5.79/2.30  BG Simplification    : 0.04
% 5.79/2.30  Subsumption          : 0.12
% 5.79/2.30  Abstraction          : 0.04
% 5.79/2.30  MUC search           : 0.00
% 5.79/2.30  Cooper               : 0.00
% 5.79/2.30  Total                : 1.41
% 5.79/2.30  Index Insertion      : 0.00
% 5.79/2.30  Index Deletion       : 0.00
% 5.79/2.30  Index Matching       : 0.00
% 5.79/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
