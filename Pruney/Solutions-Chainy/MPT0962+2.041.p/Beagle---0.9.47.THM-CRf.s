%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:57 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 285 expanded)
%              Number of leaves         :   24 ( 105 expanded)
%              Depth                    :    9
%              Number of atoms          :  218 ( 768 expanded)
%              Number of equality atoms :   73 ( 205 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_505,plain,(
    ! [C_135,A_136,B_137] :
      ( m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ r1_tarski(k2_relat_1(C_135),B_137)
      | ~ r1_tarski(k1_relat_1(C_135),A_136)
      | ~ v1_relat_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_74,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) = k1_xboole_0
      | k1_relat_1(A_20) != k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_74])).

tff(c_79,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_40,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36])).

tff(c_80,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_139,plain,(
    ! [C_40,A_41,B_42] :
      ( m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ r1_tarski(k2_relat_1(C_40),B_42)
      | ~ r1_tarski(k1_relat_1(C_40),A_41)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] :
      ( k1_relset_1(A_7,B_8,C_9) = k1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_176,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ r1_tarski(k2_relat_1(C_53),B_52)
      | ~ r1_tarski(k1_relat_1(C_53),A_51)
      | ~ v1_relat_1(C_53) ) ),
    inference(resolution,[status(thm)],[c_139,c_20])).

tff(c_178,plain,(
    ! [A_51] :
      ( k1_relset_1(A_51,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_51)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_176])).

tff(c_198,plain,(
    ! [A_57] :
      ( k1_relset_1(A_57,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_178])).

tff(c_203,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_198])).

tff(c_22,plain,(
    ! [C_12,A_10,B_11] :
      ( m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ r1_tarski(k2_relat_1(C_12),B_11)
      | ~ r1_tarski(k1_relat_1(C_12),A_10)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_151,plain,(
    ! [B_45,C_46,A_47] :
      ( k1_xboole_0 = B_45
      | v1_funct_2(C_46,A_47,B_45)
      | k1_relset_1(A_47,B_45,C_46) != A_47
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_222,plain,(
    ! [B_61,C_62,A_63] :
      ( k1_xboole_0 = B_61
      | v1_funct_2(C_62,A_63,B_61)
      | k1_relset_1(A_63,B_61,C_62) != A_63
      | ~ r1_tarski(k2_relat_1(C_62),B_61)
      | ~ r1_tarski(k1_relat_1(C_62),A_63)
      | ~ v1_relat_1(C_62) ) ),
    inference(resolution,[status(thm)],[c_22,c_151])).

tff(c_224,plain,(
    ! [A_63] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_63,'#skF_1')
      | k1_relset_1(A_63,'#skF_1','#skF_2') != A_63
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_63)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_222])).

tff(c_230,plain,(
    ! [A_63] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_63,'#skF_1')
      | k1_relset_1(A_63,'#skF_1','#skF_2') != A_63
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_224])).

tff(c_232,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_253,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_8])).

tff(c_81,plain,(
    ! [B_21,A_22] :
      ( B_21 = A_22
      | ~ r1_tarski(B_21,A_22)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_81])).

tff(c_107,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_107])).

tff(c_264,plain,(
    ! [A_67] :
      ( v1_funct_2('#skF_2',A_67,'#skF_1')
      | k1_relset_1(A_67,'#skF_1','#skF_2') != A_67
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_67) ) ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_268,plain,
    ( v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_264])).

tff(c_271,plain,(
    v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_268])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_271])).

tff(c_274,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_294,plain,(
    ! [A_70] :
      ( k1_relat_1(A_70) = k1_xboole_0
      | k2_relat_1(A_70) != k1_xboole_0
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_297,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_294])).

tff(c_299,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_297])).

tff(c_300,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_299])).

tff(c_313,plain,(
    ! [C_82,A_83,B_84] :
      ( m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ r1_tarski(k2_relat_1(C_82),B_84)
      | ~ r1_tarski(k1_relat_1(C_82),A_83)
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_367,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ r1_tarski(k2_relat_1(C_100),B_99)
      | ~ r1_tarski(k1_relat_1(C_100),A_98)
      | ~ v1_relat_1(C_100) ) ),
    inference(resolution,[status(thm)],[c_313,c_20])).

tff(c_376,plain,(
    ! [A_101,C_102] :
      ( k1_relset_1(A_101,k2_relat_1(C_102),C_102) = k1_relat_1(C_102)
      | ~ r1_tarski(k1_relat_1(C_102),A_101)
      | ~ v1_relat_1(C_102) ) ),
    inference(resolution,[status(thm)],[c_6,c_367])).

tff(c_381,plain,(
    ! [C_103] :
      ( k1_relset_1(k1_relat_1(C_103),k2_relat_1(C_103),C_103) = k1_relat_1(C_103)
      | ~ v1_relat_1(C_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_376])).

tff(c_390,plain,
    ( k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_381])).

tff(c_394,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_390])).

tff(c_341,plain,(
    ! [B_91,C_92,A_93] :
      ( k1_xboole_0 = B_91
      | v1_funct_2(C_92,A_93,B_91)
      | k1_relset_1(A_93,B_91,C_92) != A_93
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_412,plain,(
    ! [B_110,C_111,A_112] :
      ( k1_xboole_0 = B_110
      | v1_funct_2(C_111,A_112,B_110)
      | k1_relset_1(A_112,B_110,C_111) != A_112
      | ~ r1_tarski(k2_relat_1(C_111),B_110)
      | ~ r1_tarski(k1_relat_1(C_111),A_112)
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_22,c_341])).

tff(c_414,plain,(
    ! [B_110,A_112] :
      ( k1_xboole_0 = B_110
      | v1_funct_2('#skF_2',A_112,B_110)
      | k1_relset_1(A_112,B_110,'#skF_2') != A_112
      | ~ r1_tarski('#skF_1',B_110)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_112)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_412])).

tff(c_421,plain,(
    ! [B_113,A_114] :
      ( k1_xboole_0 = B_113
      | v1_funct_2('#skF_2',A_114,B_113)
      | k1_relset_1(A_114,B_113,'#skF_2') != A_114
      | ~ r1_tarski('#skF_1',B_113)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_414])).

tff(c_426,plain,(
    ! [B_115] :
      ( k1_xboole_0 = B_115
      | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),B_115)
      | k1_relset_1(k1_relat_1('#skF_2'),B_115,'#skF_2') != k1_relat_1('#skF_2')
      | ~ r1_tarski('#skF_1',B_115) ) ),
    inference(resolution,[status(thm)],[c_6,c_421])).

tff(c_434,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_426,c_80])).

tff(c_442,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_394,c_434])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_442])).

tff(c_445,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_511,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_505,c_445])).

tff(c_522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_38,c_511])).

tff(c_524,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_523,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_591,plain,(
    ! [C_157,A_158,B_159] :
      ( m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ r1_tarski(k2_relat_1(C_157),B_159)
      | ~ r1_tarski(k1_relat_1(C_157),A_158)
      | ~ v1_relat_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_602,plain,(
    ! [C_160,A_161] :
      ( m1_subset_1(C_160,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_160),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_160),A_161)
      | ~ v1_relat_1(C_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_591])).

tff(c_604,plain,(
    ! [A_161] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_161)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_602])).

tff(c_606,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_524,c_6,c_604])).

tff(c_579,plain,(
    ! [A_144,B_145,C_146] :
      ( k1_relset_1(A_144,B_145,C_146) = k1_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_585,plain,(
    ! [B_5,C_146] :
      ( k1_relset_1(k1_xboole_0,B_5,C_146) = k1_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_579])).

tff(c_610,plain,(
    ! [B_5] : k1_relset_1(k1_xboole_0,B_5,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_606,c_585])).

tff(c_615,plain,(
    ! [B_5] : k1_relset_1(k1_xboole_0,B_5,'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_610])).

tff(c_28,plain,(
    ! [C_15,B_14] :
      ( v1_funct_2(C_15,k1_xboole_0,B_14)
      | k1_relset_1(k1_xboole_0,B_14,C_15) != k1_xboole_0
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_45,plain,(
    ! [C_15,B_14] :
      ( v1_funct_2(C_15,k1_xboole_0,B_14)
      | k1_relset_1(k1_xboole_0,B_14,C_15) != k1_xboole_0
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_613,plain,(
    ! [B_14] :
      ( v1_funct_2('#skF_2',k1_xboole_0,B_14)
      | k1_relset_1(k1_xboole_0,B_14,'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_606,c_45])).

tff(c_626,plain,(
    ! [B_14] : v1_funct_2('#skF_2',k1_xboole_0,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_613])).

tff(c_525,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_536,plain,(
    ~ v1_funct_2('#skF_2',k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_525])).

tff(c_629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_536])).

tff(c_630,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_643,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_524,c_630])).

tff(c_701,plain,(
    ! [C_182,A_183,B_184] :
      ( m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ r1_tarski(k2_relat_1(C_182),B_184)
      | ~ r1_tarski(k1_relat_1(C_182),A_183)
      | ~ v1_relat_1(C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_712,plain,(
    ! [C_185,A_186] :
      ( m1_subset_1(C_185,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_185),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_185),A_186)
      | ~ v1_relat_1(C_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_701])).

tff(c_714,plain,(
    ! [A_186] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_186)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_712])).

tff(c_716,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_524,c_6,c_714])).

tff(c_718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:13:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.41  
% 2.67/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.41  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.67/1.41  
% 2.67/1.41  %Foreground sorts:
% 2.67/1.41  
% 2.67/1.41  
% 2.67/1.41  %Background operators:
% 2.67/1.41  
% 2.67/1.41  
% 2.67/1.41  %Foreground operators:
% 2.67/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.67/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.67/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.41  
% 2.67/1.43  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.67/1.43  tff(f_88, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.67/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.67/1.43  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.67/1.43  tff(f_45, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.67/1.43  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.67/1.43  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.67/1.43  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.67/1.43  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.67/1.43  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.67/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.43  tff(c_38, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.67/1.43  tff(c_505, plain, (![C_135, A_136, B_137]: (m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~r1_tarski(k2_relat_1(C_135), B_137) | ~r1_tarski(k1_relat_1(C_135), A_136) | ~v1_relat_1(C_135))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.43  tff(c_74, plain, (![A_20]: (k2_relat_1(A_20)=k1_xboole_0 | k1_relat_1(A_20)!=k1_xboole_0 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.43  tff(c_78, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_74])).
% 2.67/1.43  tff(c_79, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_78])).
% 2.67/1.43  tff(c_40, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.67/1.43  tff(c_36, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.67/1.43  tff(c_44, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 2.67/1.43  tff(c_80, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 2.67/1.43  tff(c_139, plain, (![C_40, A_41, B_42]: (m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~r1_tarski(k2_relat_1(C_40), B_42) | ~r1_tarski(k1_relat_1(C_40), A_41) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.43  tff(c_20, plain, (![A_7, B_8, C_9]: (k1_relset_1(A_7, B_8, C_9)=k1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.67/1.43  tff(c_176, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~r1_tarski(k2_relat_1(C_53), B_52) | ~r1_tarski(k1_relat_1(C_53), A_51) | ~v1_relat_1(C_53))), inference(resolution, [status(thm)], [c_139, c_20])).
% 2.67/1.43  tff(c_178, plain, (![A_51]: (k1_relset_1(A_51, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_51) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_176])).
% 2.67/1.43  tff(c_198, plain, (![A_57]: (k1_relset_1(A_57, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_57))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_178])).
% 2.67/1.43  tff(c_203, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_198])).
% 2.67/1.43  tff(c_22, plain, (![C_12, A_10, B_11]: (m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~r1_tarski(k2_relat_1(C_12), B_11) | ~r1_tarski(k1_relat_1(C_12), A_10) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.43  tff(c_151, plain, (![B_45, C_46, A_47]: (k1_xboole_0=B_45 | v1_funct_2(C_46, A_47, B_45) | k1_relset_1(A_47, B_45, C_46)!=A_47 | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_45))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.67/1.43  tff(c_222, plain, (![B_61, C_62, A_63]: (k1_xboole_0=B_61 | v1_funct_2(C_62, A_63, B_61) | k1_relset_1(A_63, B_61, C_62)!=A_63 | ~r1_tarski(k2_relat_1(C_62), B_61) | ~r1_tarski(k1_relat_1(C_62), A_63) | ~v1_relat_1(C_62))), inference(resolution, [status(thm)], [c_22, c_151])).
% 2.67/1.43  tff(c_224, plain, (![A_63]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_63, '#skF_1') | k1_relset_1(A_63, '#skF_1', '#skF_2')!=A_63 | ~r1_tarski(k1_relat_1('#skF_2'), A_63) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_222])).
% 2.67/1.43  tff(c_230, plain, (![A_63]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_63, '#skF_1') | k1_relset_1(A_63, '#skF_1', '#skF_2')!=A_63 | ~r1_tarski(k1_relat_1('#skF_2'), A_63))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_224])).
% 2.67/1.43  tff(c_232, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_230])).
% 2.67/1.43  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.43  tff(c_253, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_8])).
% 2.67/1.43  tff(c_81, plain, (![B_21, A_22]: (B_21=A_22 | ~r1_tarski(B_21, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.43  tff(c_88, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_81])).
% 2.67/1.43  tff(c_107, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_88])).
% 2.67/1.43  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_253, c_107])).
% 2.67/1.43  tff(c_264, plain, (![A_67]: (v1_funct_2('#skF_2', A_67, '#skF_1') | k1_relset_1(A_67, '#skF_1', '#skF_2')!=A_67 | ~r1_tarski(k1_relat_1('#skF_2'), A_67))), inference(splitRight, [status(thm)], [c_230])).
% 2.67/1.43  tff(c_268, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_264])).
% 2.67/1.43  tff(c_271, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_268])).
% 2.67/1.43  tff(c_273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_271])).
% 2.67/1.43  tff(c_274, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_88])).
% 2.67/1.43  tff(c_294, plain, (![A_70]: (k1_relat_1(A_70)=k1_xboole_0 | k2_relat_1(A_70)!=k1_xboole_0 | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.43  tff(c_297, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k2_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_294])).
% 2.67/1.43  tff(c_299, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_274, c_297])).
% 2.67/1.43  tff(c_300, plain, (k1_xboole_0!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_79, c_299])).
% 2.67/1.43  tff(c_313, plain, (![C_82, A_83, B_84]: (m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~r1_tarski(k2_relat_1(C_82), B_84) | ~r1_tarski(k1_relat_1(C_82), A_83) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.43  tff(c_367, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~r1_tarski(k2_relat_1(C_100), B_99) | ~r1_tarski(k1_relat_1(C_100), A_98) | ~v1_relat_1(C_100))), inference(resolution, [status(thm)], [c_313, c_20])).
% 2.67/1.43  tff(c_376, plain, (![A_101, C_102]: (k1_relset_1(A_101, k2_relat_1(C_102), C_102)=k1_relat_1(C_102) | ~r1_tarski(k1_relat_1(C_102), A_101) | ~v1_relat_1(C_102))), inference(resolution, [status(thm)], [c_6, c_367])).
% 2.67/1.43  tff(c_381, plain, (![C_103]: (k1_relset_1(k1_relat_1(C_103), k2_relat_1(C_103), C_103)=k1_relat_1(C_103) | ~v1_relat_1(C_103))), inference(resolution, [status(thm)], [c_6, c_376])).
% 2.67/1.43  tff(c_390, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_274, c_381])).
% 2.67/1.43  tff(c_394, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_390])).
% 2.67/1.43  tff(c_341, plain, (![B_91, C_92, A_93]: (k1_xboole_0=B_91 | v1_funct_2(C_92, A_93, B_91) | k1_relset_1(A_93, B_91, C_92)!=A_93 | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.67/1.43  tff(c_412, plain, (![B_110, C_111, A_112]: (k1_xboole_0=B_110 | v1_funct_2(C_111, A_112, B_110) | k1_relset_1(A_112, B_110, C_111)!=A_112 | ~r1_tarski(k2_relat_1(C_111), B_110) | ~r1_tarski(k1_relat_1(C_111), A_112) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_22, c_341])).
% 2.67/1.43  tff(c_414, plain, (![B_110, A_112]: (k1_xboole_0=B_110 | v1_funct_2('#skF_2', A_112, B_110) | k1_relset_1(A_112, B_110, '#skF_2')!=A_112 | ~r1_tarski('#skF_1', B_110) | ~r1_tarski(k1_relat_1('#skF_2'), A_112) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_412])).
% 2.67/1.43  tff(c_421, plain, (![B_113, A_114]: (k1_xboole_0=B_113 | v1_funct_2('#skF_2', A_114, B_113) | k1_relset_1(A_114, B_113, '#skF_2')!=A_114 | ~r1_tarski('#skF_1', B_113) | ~r1_tarski(k1_relat_1('#skF_2'), A_114))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_414])).
% 2.67/1.43  tff(c_426, plain, (![B_115]: (k1_xboole_0=B_115 | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), B_115) | k1_relset_1(k1_relat_1('#skF_2'), B_115, '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski('#skF_1', B_115))), inference(resolution, [status(thm)], [c_6, c_421])).
% 2.67/1.43  tff(c_434, plain, (k1_xboole_0='#skF_1' | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_426, c_80])).
% 2.67/1.43  tff(c_442, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_394, c_434])).
% 2.67/1.43  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_442])).
% 2.67/1.43  tff(c_445, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_44])).
% 2.67/1.43  tff(c_511, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_505, c_445])).
% 2.67/1.43  tff(c_522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_38, c_511])).
% 2.67/1.43  tff(c_524, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 2.67/1.43  tff(c_523, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 2.67/1.43  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.67/1.43  tff(c_591, plain, (![C_157, A_158, B_159]: (m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~r1_tarski(k2_relat_1(C_157), B_159) | ~r1_tarski(k1_relat_1(C_157), A_158) | ~v1_relat_1(C_157))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.43  tff(c_602, plain, (![C_160, A_161]: (m1_subset_1(C_160, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_160), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_160), A_161) | ~v1_relat_1(C_160))), inference(superposition, [status(thm), theory('equality')], [c_12, c_591])).
% 2.67/1.43  tff(c_604, plain, (![A_161]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_161) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_523, c_602])).
% 2.67/1.43  tff(c_606, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_524, c_6, c_604])).
% 2.67/1.43  tff(c_579, plain, (![A_144, B_145, C_146]: (k1_relset_1(A_144, B_145, C_146)=k1_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.67/1.43  tff(c_585, plain, (![B_5, C_146]: (k1_relset_1(k1_xboole_0, B_5, C_146)=k1_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_579])).
% 2.67/1.43  tff(c_610, plain, (![B_5]: (k1_relset_1(k1_xboole_0, B_5, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_606, c_585])).
% 2.67/1.43  tff(c_615, plain, (![B_5]: (k1_relset_1(k1_xboole_0, B_5, '#skF_2')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_524, c_610])).
% 2.67/1.43  tff(c_28, plain, (![C_15, B_14]: (v1_funct_2(C_15, k1_xboole_0, B_14) | k1_relset_1(k1_xboole_0, B_14, C_15)!=k1_xboole_0 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.67/1.43  tff(c_45, plain, (![C_15, B_14]: (v1_funct_2(C_15, k1_xboole_0, B_14) | k1_relset_1(k1_xboole_0, B_14, C_15)!=k1_xboole_0 | ~m1_subset_1(C_15, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 2.67/1.43  tff(c_613, plain, (![B_14]: (v1_funct_2('#skF_2', k1_xboole_0, B_14) | k1_relset_1(k1_xboole_0, B_14, '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_606, c_45])).
% 2.67/1.43  tff(c_626, plain, (![B_14]: (v1_funct_2('#skF_2', k1_xboole_0, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_615, c_613])).
% 2.67/1.43  tff(c_525, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 2.67/1.43  tff(c_536, plain, (~v1_funct_2('#skF_2', k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_525])).
% 2.67/1.43  tff(c_629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_626, c_536])).
% 2.67/1.43  tff(c_630, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_44])).
% 2.67/1.43  tff(c_643, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_524, c_630])).
% 2.67/1.43  tff(c_701, plain, (![C_182, A_183, B_184]: (m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~r1_tarski(k2_relat_1(C_182), B_184) | ~r1_tarski(k1_relat_1(C_182), A_183) | ~v1_relat_1(C_182))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.43  tff(c_712, plain, (![C_185, A_186]: (m1_subset_1(C_185, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_185), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_185), A_186) | ~v1_relat_1(C_185))), inference(superposition, [status(thm), theory('equality')], [c_12, c_701])).
% 2.67/1.43  tff(c_714, plain, (![A_186]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_186) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_523, c_712])).
% 2.67/1.43  tff(c_716, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_524, c_6, c_714])).
% 2.67/1.43  tff(c_718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_643, c_716])).
% 2.67/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.43  
% 2.67/1.43  Inference rules
% 2.67/1.43  ----------------------
% 2.67/1.43  #Ref     : 0
% 2.67/1.43  #Sup     : 130
% 2.67/1.43  #Fact    : 0
% 2.67/1.43  #Define  : 0
% 2.67/1.43  #Split   : 14
% 2.67/1.43  #Chain   : 0
% 2.67/1.43  #Close   : 0
% 2.67/1.43  
% 2.67/1.43  Ordering : KBO
% 2.67/1.43  
% 2.67/1.43  Simplification rules
% 3.04/1.43  ----------------------
% 3.04/1.43  #Subsume      : 8
% 3.04/1.43  #Demod        : 100
% 3.04/1.43  #Tautology    : 63
% 3.04/1.43  #SimpNegUnit  : 7
% 3.04/1.43  #BackRed      : 26
% 3.04/1.43  
% 3.04/1.43  #Partial instantiations: 0
% 3.04/1.43  #Strategies tried      : 1
% 3.04/1.43  
% 3.04/1.43  Timing (in seconds)
% 3.04/1.43  ----------------------
% 3.04/1.43  Preprocessing        : 0.31
% 3.04/1.43  Parsing              : 0.16
% 3.04/1.43  CNF conversion       : 0.02
% 3.04/1.43  Main loop            : 0.35
% 3.04/1.43  Inferencing          : 0.13
% 3.04/1.43  Reduction            : 0.10
% 3.04/1.43  Demodulation         : 0.07
% 3.04/1.43  BG Simplification    : 0.02
% 3.04/1.43  Subsumption          : 0.07
% 3.04/1.43  Abstraction          : 0.02
% 3.04/1.43  MUC search           : 0.00
% 3.04/1.43  Cooper               : 0.00
% 3.04/1.43  Total                : 0.70
% 3.04/1.43  Index Insertion      : 0.00
% 3.04/1.43  Index Deletion       : 0.00
% 3.04/1.43  Index Matching       : 0.00
% 3.04/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
