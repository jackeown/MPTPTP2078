%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:42 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 458 expanded)
%              Number of leaves         :   28 ( 165 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 (1159 expanded)
%              Number of equality atoms :   45 ( 356 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3946,plain,(
    ! [A_272] :
      ( r1_tarski(A_272,k2_zfmisc_1(k1_relat_1(A_272),k2_relat_1(A_272)))
      | ~ v1_relat_1(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_323,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_589,plain,(
    ! [A_113,B_114,A_115] :
      ( k1_relset_1(A_113,B_114,A_115) = k1_relat_1(A_115)
      | ~ r1_tarski(A_115,k2_zfmisc_1(A_113,B_114)) ) ),
    inference(resolution,[status(thm)],[c_18,c_323])).

tff(c_611,plain,(
    ! [A_10] :
      ( k1_relset_1(k1_relat_1(A_10),k2_relat_1(A_10),A_10) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_24,c_589])).

tff(c_535,plain,(
    ! [B_103,C_104,A_105] :
      ( k1_xboole_0 = B_103
      | v1_funct_2(C_104,A_105,B_103)
      | k1_relset_1(A_105,B_103,C_104) != A_105
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2140,plain,(
    ! [B_218,A_219,A_220] :
      ( k1_xboole_0 = B_218
      | v1_funct_2(A_219,A_220,B_218)
      | k1_relset_1(A_220,B_218,A_219) != A_220
      | ~ r1_tarski(A_219,k2_zfmisc_1(A_220,B_218)) ) ),
    inference(resolution,[status(thm)],[c_18,c_535])).

tff(c_3191,plain,(
    ! [A_242] :
      ( k2_relat_1(A_242) = k1_xboole_0
      | v1_funct_2(A_242,k1_relat_1(A_242),k2_relat_1(A_242))
      | k1_relset_1(k1_relat_1(A_242),k2_relat_1(A_242),A_242) != k1_relat_1(A_242)
      | ~ v1_relat_1(A_242) ) ),
    inference(resolution,[status(thm)],[c_24,c_2140])).

tff(c_48,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_98,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_3198,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3191,c_98])).

tff(c_3225,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3198])).

tff(c_3339,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3225])).

tff(c_3342,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_3339])).

tff(c_3346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3342])).

tff(c_3347,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3225])).

tff(c_270,plain,(
    ! [A_71] :
      ( r1_tarski(A_71,k2_zfmisc_1(k1_relat_1(A_71),k2_relat_1(A_71)))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_286,plain,(
    ! [A_71] :
      ( k2_zfmisc_1(k1_relat_1(A_71),k2_relat_1(A_71)) = A_71
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_71),k2_relat_1(A_71)),A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_270,c_2])).

tff(c_3356,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) = '#skF_1'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0),'#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3347,c_286])).

tff(c_3371,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8,c_12,c_12,c_3347,c_3356])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_133,plain,(
    ! [C_39] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_123])).

tff(c_151,plain,(
    ! [A_43] :
      ( v1_relat_1(A_43)
      | ~ r1_tarski(A_43,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_133])).

tff(c_160,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_151])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_139,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_297,plain,(
    ! [A_75,A_76,B_77] :
      ( v4_relat_1(A_75,A_76)
      | ~ r1_tarski(A_75,k2_zfmisc_1(A_76,B_77)) ) ),
    inference(resolution,[status(thm)],[c_18,c_139])).

tff(c_321,plain,(
    ! [A_76,B_77] : v4_relat_1(k2_zfmisc_1(A_76,B_77),A_76) ),
    inference(resolution,[status(thm)],[c_6,c_297])).

tff(c_201,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k1_relat_1(B_60),A_61)
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_345,plain,(
    ! [B_84] :
      ( k1_relat_1(B_84) = k1_xboole_0
      | ~ v4_relat_1(B_84,k1_xboole_0)
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_201,c_97])).

tff(c_349,plain,(
    ! [B_77] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_77)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_77)) ) ),
    inference(resolution,[status(thm)],[c_321,c_345])).

tff(c_360,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_14,c_14,c_349])).

tff(c_610,plain,(
    ! [A_113,B_114] : k1_relset_1(A_113,B_114,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_589])).

tff(c_615,plain,(
    ! [A_113,B_114] : k1_relset_1(A_113,B_114,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_610])).

tff(c_34,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_20,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_55,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_390,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_393,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_390])).

tff(c_397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_393])).

tff(c_399,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_38,plain,(
    ! [C_22,B_21] :
      ( v1_funct_2(C_22,k1_xboole_0,B_21)
      | k1_relset_1(k1_xboole_0,B_21,C_22) != k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_788,plain,(
    ! [C_140,B_141] :
      ( v1_funct_2(C_140,k1_xboole_0,B_141)
      | k1_relset_1(k1_xboole_0,B_141,C_140) != k1_xboole_0
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_790,plain,(
    ! [B_141] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_141)
      | k1_relset_1(k1_xboole_0,B_141,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_399,c_788])).

tff(c_796,plain,(
    ! [B_141] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_790])).

tff(c_3409,plain,(
    ! [B_141] : v1_funct_2('#skF_1','#skF_1',B_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3371,c_3371,c_796])).

tff(c_3427,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3371,c_3371,c_360])).

tff(c_3349,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3347,c_98])).

tff(c_3601,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3427,c_3371,c_3349])).

tff(c_3857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3409,c_3601])).

tff(c_3858,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3938,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18,c_3858])).

tff(c_3953,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3946,c_3938])).

tff(c_3963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3953])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:34:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/1.90  
% 5.08/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/1.91  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 5.08/1.91  
% 5.08/1.91  %Foreground sorts:
% 5.08/1.91  
% 5.08/1.91  
% 5.08/1.91  %Background operators:
% 5.08/1.91  
% 5.08/1.91  
% 5.08/1.91  %Foreground operators:
% 5.08/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.08/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.08/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.08/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.08/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.08/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.08/1.91  tff('#skF_1', type, '#skF_1': $i).
% 5.08/1.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.08/1.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.08/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.08/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.08/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.08/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.08/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.08/1.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.08/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.08/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.08/1.91  
% 5.08/1.92  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.08/1.92  tff(f_53, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 5.08/1.92  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.08/1.92  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.08/1.92  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.08/1.92  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.08/1.92  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.08/1.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.08/1.92  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.08/1.92  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.08/1.92  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.08/1.92  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.08/1.92  tff(c_3946, plain, (![A_272]: (r1_tarski(A_272, k2_zfmisc_1(k1_relat_1(A_272), k2_relat_1(A_272))) | ~v1_relat_1(A_272))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/1.92  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.08/1.92  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.08/1.92  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.08/1.92  tff(c_24, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/1.92  tff(c_323, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.08/1.92  tff(c_589, plain, (![A_113, B_114, A_115]: (k1_relset_1(A_113, B_114, A_115)=k1_relat_1(A_115) | ~r1_tarski(A_115, k2_zfmisc_1(A_113, B_114)))), inference(resolution, [status(thm)], [c_18, c_323])).
% 5.08/1.92  tff(c_611, plain, (![A_10]: (k1_relset_1(k1_relat_1(A_10), k2_relat_1(A_10), A_10)=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_24, c_589])).
% 5.08/1.92  tff(c_535, plain, (![B_103, C_104, A_105]: (k1_xboole_0=B_103 | v1_funct_2(C_104, A_105, B_103) | k1_relset_1(A_105, B_103, C_104)!=A_105 | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_103))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.08/1.92  tff(c_2140, plain, (![B_218, A_219, A_220]: (k1_xboole_0=B_218 | v1_funct_2(A_219, A_220, B_218) | k1_relset_1(A_220, B_218, A_219)!=A_220 | ~r1_tarski(A_219, k2_zfmisc_1(A_220, B_218)))), inference(resolution, [status(thm)], [c_18, c_535])).
% 5.08/1.92  tff(c_3191, plain, (![A_242]: (k2_relat_1(A_242)=k1_xboole_0 | v1_funct_2(A_242, k1_relat_1(A_242), k2_relat_1(A_242)) | k1_relset_1(k1_relat_1(A_242), k2_relat_1(A_242), A_242)!=k1_relat_1(A_242) | ~v1_relat_1(A_242))), inference(resolution, [status(thm)], [c_24, c_2140])).
% 5.08/1.92  tff(c_48, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.08/1.92  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.08/1.92  tff(c_52, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 5.08/1.92  tff(c_98, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 5.08/1.92  tff(c_3198, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3191, c_98])).
% 5.08/1.92  tff(c_3225, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3198])).
% 5.08/1.92  tff(c_3339, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_3225])).
% 5.08/1.92  tff(c_3342, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_611, c_3339])).
% 5.08/1.92  tff(c_3346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_3342])).
% 5.08/1.92  tff(c_3347, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3225])).
% 5.08/1.92  tff(c_270, plain, (![A_71]: (r1_tarski(A_71, k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71))) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/1.92  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.08/1.92  tff(c_286, plain, (![A_71]: (k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71))=A_71 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71)), A_71) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_270, c_2])).
% 5.08/1.92  tff(c_3356, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0), '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3347, c_286])).
% 5.08/1.92  tff(c_3371, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8, c_12, c_12, c_3347, c_3356])).
% 5.08/1.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.08/1.92  tff(c_123, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.08/1.92  tff(c_133, plain, (![C_39]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_123])).
% 5.08/1.92  tff(c_151, plain, (![A_43]: (v1_relat_1(A_43) | ~r1_tarski(A_43, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_133])).
% 5.08/1.92  tff(c_160, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_151])).
% 5.08/1.92  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.08/1.92  tff(c_139, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.08/1.92  tff(c_297, plain, (![A_75, A_76, B_77]: (v4_relat_1(A_75, A_76) | ~r1_tarski(A_75, k2_zfmisc_1(A_76, B_77)))), inference(resolution, [status(thm)], [c_18, c_139])).
% 5.08/1.92  tff(c_321, plain, (![A_76, B_77]: (v4_relat_1(k2_zfmisc_1(A_76, B_77), A_76))), inference(resolution, [status(thm)], [c_6, c_297])).
% 5.08/1.92  tff(c_201, plain, (![B_60, A_61]: (r1_tarski(k1_relat_1(B_60), A_61) | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.08/1.92  tff(c_88, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.08/1.92  tff(c_97, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_88])).
% 5.08/1.92  tff(c_345, plain, (![B_84]: (k1_relat_1(B_84)=k1_xboole_0 | ~v4_relat_1(B_84, k1_xboole_0) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_201, c_97])).
% 5.08/1.92  tff(c_349, plain, (![B_77]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_77))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_77)))), inference(resolution, [status(thm)], [c_321, c_345])).
% 5.08/1.92  tff(c_360, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_160, c_14, c_14, c_349])).
% 5.08/1.92  tff(c_610, plain, (![A_113, B_114]: (k1_relset_1(A_113, B_114, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_589])).
% 5.08/1.92  tff(c_615, plain, (![A_113, B_114]: (k1_relset_1(A_113, B_114, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_360, c_610])).
% 5.08/1.92  tff(c_34, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_20, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.08/1.92  tff(c_55, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 5.08/1.92  tff(c_390, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_55])).
% 5.08/1.92  tff(c_393, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_390])).
% 5.08/1.92  tff(c_397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_393])).
% 5.08/1.92  tff(c_399, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_55])).
% 5.08/1.92  tff(c_38, plain, (![C_22, B_21]: (v1_funct_2(C_22, k1_xboole_0, B_21) | k1_relset_1(k1_xboole_0, B_21, C_22)!=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.08/1.92  tff(c_788, plain, (![C_140, B_141]: (v1_funct_2(C_140, k1_xboole_0, B_141) | k1_relset_1(k1_xboole_0, B_141, C_140)!=k1_xboole_0 | ~m1_subset_1(C_140, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 5.08/1.92  tff(c_790, plain, (![B_141]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_141) | k1_relset_1(k1_xboole_0, B_141, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_399, c_788])).
% 5.08/1.92  tff(c_796, plain, (![B_141]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_141))), inference(demodulation, [status(thm), theory('equality')], [c_615, c_790])).
% 5.08/1.92  tff(c_3409, plain, (![B_141]: (v1_funct_2('#skF_1', '#skF_1', B_141))), inference(demodulation, [status(thm), theory('equality')], [c_3371, c_3371, c_796])).
% 5.08/1.92  tff(c_3427, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3371, c_3371, c_360])).
% 5.08/1.92  tff(c_3349, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3347, c_98])).
% 5.08/1.92  tff(c_3601, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3427, c_3371, c_3349])).
% 5.08/1.92  tff(c_3857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3409, c_3601])).
% 5.08/1.92  tff(c_3858, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_52])).
% 5.08/1.92  tff(c_3938, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_3858])).
% 5.08/1.92  tff(c_3953, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3946, c_3938])).
% 5.08/1.92  tff(c_3963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_3953])).
% 5.08/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/1.92  
% 5.08/1.92  Inference rules
% 5.08/1.92  ----------------------
% 5.08/1.92  #Ref     : 0
% 5.08/1.92  #Sup     : 821
% 5.08/1.92  #Fact    : 0
% 5.08/1.92  #Define  : 0
% 5.08/1.92  #Split   : 3
% 5.08/1.92  #Chain   : 0
% 5.08/1.92  #Close   : 0
% 5.08/1.92  
% 5.08/1.92  Ordering : KBO
% 5.08/1.92  
% 5.08/1.92  Simplification rules
% 5.08/1.92  ----------------------
% 5.08/1.92  #Subsume      : 126
% 5.08/1.92  #Demod        : 1289
% 5.08/1.92  #Tautology    : 394
% 5.08/1.92  #SimpNegUnit  : 0
% 5.08/1.92  #BackRed      : 66
% 5.08/1.92  
% 5.08/1.92  #Partial instantiations: 0
% 5.08/1.92  #Strategies tried      : 1
% 5.08/1.92  
% 5.08/1.92  Timing (in seconds)
% 5.08/1.92  ----------------------
% 5.08/1.93  Preprocessing        : 0.32
% 5.08/1.93  Parsing              : 0.17
% 5.08/1.93  CNF conversion       : 0.02
% 5.08/1.93  Main loop            : 0.82
% 5.08/1.93  Inferencing          : 0.27
% 5.08/1.93  Reduction            : 0.30
% 5.08/1.93  Demodulation         : 0.23
% 5.08/1.93  BG Simplification    : 0.04
% 5.08/1.93  Subsumption          : 0.16
% 5.08/1.93  Abstraction          : 0.05
% 5.08/1.93  MUC search           : 0.00
% 5.08/1.93  Cooper               : 0.00
% 5.08/1.93  Total                : 1.18
% 5.08/1.93  Index Insertion      : 0.00
% 5.08/1.93  Index Deletion       : 0.00
% 5.08/1.93  Index Matching       : 0.00
% 5.08/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
