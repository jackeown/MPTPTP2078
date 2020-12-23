%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:48 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 279 expanded)
%              Number of leaves         :   28 ( 103 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 645 expanded)
%              Number of equality atoms :   55 ( 245 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

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

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1259,plain,(
    ! [C_185,A_186,B_187] :
      ( m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ r1_tarski(k2_relat_1(C_185),B_187)
      | ~ r1_tarski(k1_relat_1(C_185),A_186)
      | ~ v1_relat_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_195,plain,(
    ! [C_42,A_43,B_44] :
      ( m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ r1_tarski(k2_relat_1(C_42),B_44)
      | ~ r1_tarski(k1_relat_1(C_42),A_43)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_479,plain,(
    ! [C_84,A_85,B_86] :
      ( r1_tarski(C_84,k2_zfmisc_1(A_85,B_86))
      | ~ r1_tarski(k2_relat_1(C_84),B_86)
      | ~ r1_tarski(k1_relat_1(C_84),A_85)
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_195,c_20])).

tff(c_487,plain,(
    ! [C_87,A_88] :
      ( r1_tarski(C_87,k2_zfmisc_1(A_88,k2_relat_1(C_87)))
      | ~ r1_tarski(k1_relat_1(C_87),A_88)
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_479])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_178,plain,(
    ! [A_39,B_40,C_41] :
      ( k1_relset_1(A_39,B_40,C_41) = k1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_193,plain,(
    ! [A_39,B_40,A_8] :
      ( k1_relset_1(A_39,B_40,A_8) = k1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_39,B_40)) ) ),
    inference(resolution,[status(thm)],[c_22,c_178])).

tff(c_562,plain,(
    ! [A_95,C_96] :
      ( k1_relset_1(A_95,k2_relat_1(C_96),C_96) = k1_relat_1(C_96)
      | ~ r1_tarski(k1_relat_1(C_96),A_95)
      | ~ v1_relat_1(C_96) ) ),
    inference(resolution,[status(thm)],[c_487,c_193])).

tff(c_572,plain,(
    ! [C_96] :
      ( k1_relset_1(k1_relat_1(C_96),k2_relat_1(C_96),C_96) = k1_relat_1(C_96)
      | ~ v1_relat_1(C_96) ) ),
    inference(resolution,[status(thm)],[c_6,c_562])).

tff(c_102,plain,(
    ! [A_28] :
      ( k2_relat_1(A_28) != k1_xboole_0
      | k1_xboole_0 = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_106,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_52,c_102])).

tff(c_107,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_486,plain,(
    ! [C_84,A_85] :
      ( r1_tarski(C_84,k2_zfmisc_1(A_85,k2_relat_1(C_84)))
      | ~ r1_tarski(k1_relat_1(C_84),A_85)
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_479])).

tff(c_411,plain,(
    ! [B_74,C_75,A_76] :
      ( k1_xboole_0 = B_74
      | v1_funct_2(C_75,A_76,B_74)
      | k1_relset_1(A_76,B_74,C_75) != A_76
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_514,plain,(
    ! [B_90,A_91,A_92] :
      ( k1_xboole_0 = B_90
      | v1_funct_2(A_91,A_92,B_90)
      | k1_relset_1(A_92,B_90,A_91) != A_92
      | ~ r1_tarski(A_91,k2_zfmisc_1(A_92,B_90)) ) ),
    inference(resolution,[status(thm)],[c_22,c_411])).

tff(c_739,plain,(
    ! [C_115,A_116] :
      ( k2_relat_1(C_115) = k1_xboole_0
      | v1_funct_2(C_115,A_116,k2_relat_1(C_115))
      | k1_relset_1(A_116,k2_relat_1(C_115),C_115) != A_116
      | ~ r1_tarski(k1_relat_1(C_115),A_116)
      | ~ v1_relat_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_486,c_514])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_99,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_752,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_739,c_99])).

tff(c_761,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6,c_752])).

tff(c_762,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_761])).

tff(c_766,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_762])).

tff(c_770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_766])).

tff(c_771,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_787,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_26])).

tff(c_18,plain,(
    ! [A_6] : m1_subset_1('#skF_1'(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_773,plain,(
    ! [A_117,B_118] :
      ( r1_tarski(A_117,B_118)
      | ~ m1_subset_1(A_117,k1_zfmisc_1(B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_781,plain,(
    ! [A_6] : r1_tarski('#skF_1'(A_6),A_6) ),
    inference(resolution,[status(thm)],[c_18,c_773])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_836,plain,(
    ! [A_123] :
      ( A_123 = '#skF_2'
      | ~ r1_tarski(A_123,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_8])).

tff(c_845,plain,(
    '#skF_1'('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_781,c_836])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_784,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_14])).

tff(c_919,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_936,plain,(
    ! [B_136,C_137] :
      ( k1_relset_1('#skF_2',B_136,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_919])).

tff(c_944,plain,(
    ! [B_136] : k1_relset_1('#skF_2',B_136,'#skF_1'('#skF_2')) = k1_relat_1('#skF_1'('#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_936])).

tff(c_949,plain,(
    ! [B_136] : k1_relset_1('#skF_2',B_136,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_845,c_845,c_944])).

tff(c_40,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_1110,plain,(
    ! [C_161,B_162] :
      ( v1_funct_2(C_161,'#skF_2',B_162)
      | k1_relset_1('#skF_2',B_162,C_161) != '#skF_2'
      | ~ m1_subset_1(C_161,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_771,c_771,c_56])).

tff(c_1118,plain,(
    ! [B_162] :
      ( v1_funct_2('#skF_1'('#skF_2'),'#skF_2',B_162)
      | k1_relset_1('#skF_2',B_162,'#skF_1'('#skF_2')) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_18,c_1110])).

tff(c_1125,plain,(
    ! [B_162] : v1_funct_2('#skF_2','#skF_2',B_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_949,c_845,c_845,c_1118])).

tff(c_772,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_792,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_772])).

tff(c_793,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_99])).

tff(c_799,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_793])).

tff(c_1128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1125,c_799])).

tff(c_1129,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1265,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1259,c_1129])).

tff(c_1279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6,c_6,c_1265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.50  
% 3.31/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.50  %$ v1_funct_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 3.31/1.50  
% 3.31/1.50  %Foreground sorts:
% 3.31/1.50  
% 3.31/1.50  
% 3.31/1.50  %Background operators:
% 3.31/1.50  
% 3.31/1.50  
% 3.31/1.50  %Foreground operators:
% 3.31/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.50  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.31/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.31/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.31/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.31/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.50  
% 3.31/1.52  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.31/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.31/1.52  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.31/1.52  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.31/1.52  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.31/1.52  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.31/1.52  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.31/1.52  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.31/1.52  tff(f_47, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 3.31/1.52  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.31/1.52  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.31/1.52  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.31/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.31/1.52  tff(c_1259, plain, (![C_185, A_186, B_187]: (m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~r1_tarski(k2_relat_1(C_185), B_187) | ~r1_tarski(k1_relat_1(C_185), A_186) | ~v1_relat_1(C_185))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.31/1.52  tff(c_195, plain, (![C_42, A_43, B_44]: (m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~r1_tarski(k2_relat_1(C_42), B_44) | ~r1_tarski(k1_relat_1(C_42), A_43) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.31/1.52  tff(c_20, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.31/1.52  tff(c_479, plain, (![C_84, A_85, B_86]: (r1_tarski(C_84, k2_zfmisc_1(A_85, B_86)) | ~r1_tarski(k2_relat_1(C_84), B_86) | ~r1_tarski(k1_relat_1(C_84), A_85) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_195, c_20])).
% 3.31/1.52  tff(c_487, plain, (![C_87, A_88]: (r1_tarski(C_87, k2_zfmisc_1(A_88, k2_relat_1(C_87))) | ~r1_tarski(k1_relat_1(C_87), A_88) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_6, c_479])).
% 3.31/1.52  tff(c_22, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.31/1.52  tff(c_178, plain, (![A_39, B_40, C_41]: (k1_relset_1(A_39, B_40, C_41)=k1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.31/1.52  tff(c_193, plain, (![A_39, B_40, A_8]: (k1_relset_1(A_39, B_40, A_8)=k1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_39, B_40)))), inference(resolution, [status(thm)], [c_22, c_178])).
% 3.31/1.52  tff(c_562, plain, (![A_95, C_96]: (k1_relset_1(A_95, k2_relat_1(C_96), C_96)=k1_relat_1(C_96) | ~r1_tarski(k1_relat_1(C_96), A_95) | ~v1_relat_1(C_96))), inference(resolution, [status(thm)], [c_487, c_193])).
% 3.31/1.52  tff(c_572, plain, (![C_96]: (k1_relset_1(k1_relat_1(C_96), k2_relat_1(C_96), C_96)=k1_relat_1(C_96) | ~v1_relat_1(C_96))), inference(resolution, [status(thm)], [c_6, c_562])).
% 3.31/1.52  tff(c_102, plain, (![A_28]: (k2_relat_1(A_28)!=k1_xboole_0 | k1_xboole_0=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.31/1.52  tff(c_106, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_52, c_102])).
% 3.31/1.52  tff(c_107, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_106])).
% 3.31/1.52  tff(c_486, plain, (![C_84, A_85]: (r1_tarski(C_84, k2_zfmisc_1(A_85, k2_relat_1(C_84))) | ~r1_tarski(k1_relat_1(C_84), A_85) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_6, c_479])).
% 3.31/1.52  tff(c_411, plain, (![B_74, C_75, A_76]: (k1_xboole_0=B_74 | v1_funct_2(C_75, A_76, B_74) | k1_relset_1(A_76, B_74, C_75)!=A_76 | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_74))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.31/1.52  tff(c_514, plain, (![B_90, A_91, A_92]: (k1_xboole_0=B_90 | v1_funct_2(A_91, A_92, B_90) | k1_relset_1(A_92, B_90, A_91)!=A_92 | ~r1_tarski(A_91, k2_zfmisc_1(A_92, B_90)))), inference(resolution, [status(thm)], [c_22, c_411])).
% 3.31/1.52  tff(c_739, plain, (![C_115, A_116]: (k2_relat_1(C_115)=k1_xboole_0 | v1_funct_2(C_115, A_116, k2_relat_1(C_115)) | k1_relset_1(A_116, k2_relat_1(C_115), C_115)!=A_116 | ~r1_tarski(k1_relat_1(C_115), A_116) | ~v1_relat_1(C_115))), inference(resolution, [status(thm)], [c_486, c_514])).
% 3.31/1.52  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.31/1.52  tff(c_48, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.31/1.52  tff(c_54, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 3.31/1.52  tff(c_99, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.31/1.52  tff(c_752, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_739, c_99])).
% 3.31/1.52  tff(c_761, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6, c_752])).
% 3.31/1.52  tff(c_762, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_107, c_761])).
% 3.31/1.52  tff(c_766, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_572, c_762])).
% 3.31/1.52  tff(c_770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_766])).
% 3.31/1.52  tff(c_771, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_106])).
% 3.31/1.52  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.31/1.52  tff(c_787, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_26])).
% 3.31/1.52  tff(c_18, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.31/1.52  tff(c_773, plain, (![A_117, B_118]: (r1_tarski(A_117, B_118) | ~m1_subset_1(A_117, k1_zfmisc_1(B_118)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.31/1.52  tff(c_781, plain, (![A_6]: (r1_tarski('#skF_1'(A_6), A_6))), inference(resolution, [status(thm)], [c_18, c_773])).
% 3.31/1.52  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.31/1.52  tff(c_836, plain, (![A_123]: (A_123='#skF_2' | ~r1_tarski(A_123, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_8])).
% 3.31/1.52  tff(c_845, plain, ('#skF_1'('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_781, c_836])).
% 3.31/1.52  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.31/1.52  tff(c_784, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_14])).
% 3.31/1.52  tff(c_919, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.31/1.52  tff(c_936, plain, (![B_136, C_137]: (k1_relset_1('#skF_2', B_136, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_784, c_919])).
% 3.31/1.52  tff(c_944, plain, (![B_136]: (k1_relset_1('#skF_2', B_136, '#skF_1'('#skF_2'))=k1_relat_1('#skF_1'('#skF_2')))), inference(resolution, [status(thm)], [c_18, c_936])).
% 3.31/1.52  tff(c_949, plain, (![B_136]: (k1_relset_1('#skF_2', B_136, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_787, c_845, c_845, c_944])).
% 3.31/1.52  tff(c_40, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.31/1.52  tff(c_56, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 3.31/1.52  tff(c_1110, plain, (![C_161, B_162]: (v1_funct_2(C_161, '#skF_2', B_162) | k1_relset_1('#skF_2', B_162, C_161)!='#skF_2' | ~m1_subset_1(C_161, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_771, c_771, c_56])).
% 3.31/1.52  tff(c_1118, plain, (![B_162]: (v1_funct_2('#skF_1'('#skF_2'), '#skF_2', B_162) | k1_relset_1('#skF_2', B_162, '#skF_1'('#skF_2'))!='#skF_2')), inference(resolution, [status(thm)], [c_18, c_1110])).
% 3.31/1.52  tff(c_1125, plain, (![B_162]: (v1_funct_2('#skF_2', '#skF_2', B_162))), inference(demodulation, [status(thm), theory('equality')], [c_949, c_845, c_845, c_1118])).
% 3.31/1.52  tff(c_772, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 3.31/1.52  tff(c_792, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_771, c_772])).
% 3.31/1.52  tff(c_793, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_792, c_99])).
% 3.31/1.52  tff(c_799, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_787, c_793])).
% 3.31/1.52  tff(c_1128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1125, c_799])).
% 3.31/1.52  tff(c_1129, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_54])).
% 3.31/1.52  tff(c_1265, plain, (~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1259, c_1129])).
% 3.31/1.52  tff(c_1279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_6, c_6, c_1265])).
% 3.31/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.52  
% 3.31/1.52  Inference rules
% 3.31/1.52  ----------------------
% 3.31/1.52  #Ref     : 0
% 3.31/1.52  #Sup     : 255
% 3.31/1.52  #Fact    : 0
% 3.31/1.52  #Define  : 0
% 3.31/1.52  #Split   : 6
% 3.31/1.52  #Chain   : 0
% 3.31/1.52  #Close   : 0
% 3.31/1.52  
% 3.31/1.52  Ordering : KBO
% 3.31/1.52  
% 3.31/1.52  Simplification rules
% 3.31/1.52  ----------------------
% 3.31/1.52  #Subsume      : 22
% 3.31/1.52  #Demod        : 312
% 3.31/1.52  #Tautology    : 147
% 3.31/1.52  #SimpNegUnit  : 1
% 3.31/1.52  #BackRed      : 9
% 3.31/1.52  
% 3.31/1.52  #Partial instantiations: 0
% 3.31/1.52  #Strategies tried      : 1
% 3.31/1.52  
% 3.31/1.52  Timing (in seconds)
% 3.31/1.52  ----------------------
% 3.31/1.52  Preprocessing        : 0.32
% 3.31/1.52  Parsing              : 0.17
% 3.31/1.52  CNF conversion       : 0.02
% 3.31/1.52  Main loop            : 0.42
% 3.31/1.52  Inferencing          : 0.15
% 3.31/1.52  Reduction            : 0.13
% 3.31/1.52  Demodulation         : 0.09
% 3.31/1.52  BG Simplification    : 0.02
% 3.31/1.52  Subsumption          : 0.09
% 3.31/1.52  Abstraction          : 0.02
% 3.31/1.52  MUC search           : 0.00
% 3.31/1.52  Cooper               : 0.00
% 3.31/1.52  Total                : 0.78
% 3.31/1.52  Index Insertion      : 0.00
% 3.31/1.52  Index Deletion       : 0.00
% 3.31/1.52  Index Matching       : 0.00
% 3.31/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
