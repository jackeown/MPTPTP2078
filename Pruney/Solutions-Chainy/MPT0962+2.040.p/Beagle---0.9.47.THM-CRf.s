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
% DateTime   : Thu Dec  3 10:10:57 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  160 (1037 expanded)
%              Number of leaves         :   24 ( 335 expanded)
%              Depth                    :   15
%              Number of atoms          :  287 (2681 expanded)
%              Number of equality atoms :   72 ( 566 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_86,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_73,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2259,plain,(
    ! [C_275,A_276,B_277] :
      ( m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277)))
      | ~ r1_tarski(k2_relat_1(C_275),B_277)
      | ~ r1_tarski(k1_relat_1(C_275),A_276)
      | ~ v1_relat_1(C_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36])).

tff(c_80,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_231,plain,(
    ! [C_49,A_50,B_51] :
      ( m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ r1_tarski(k2_relat_1(C_49),B_51)
      | ~ r1_tarski(k1_relat_1(C_49),A_50)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_346,plain,(
    ! [C_73,A_74,B_75] :
      ( r1_tarski(C_73,k2_zfmisc_1(A_74,B_75))
      | ~ r1_tarski(k2_relat_1(C_73),B_75)
      | ~ r1_tarski(k1_relat_1(C_73),A_74)
      | ~ v1_relat_1(C_73) ) ),
    inference(resolution,[status(thm)],[c_231,c_16])).

tff(c_348,plain,(
    ! [A_74] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_74,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_74)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_346])).

tff(c_366,plain,(
    ! [A_79] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_79,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_348])).

tff(c_371,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_366])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_145,plain,(
    ! [A_30,B_31,A_6] :
      ( k1_relset_1(A_30,B_31,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_30,B_31)) ) ),
    inference(resolution,[status(thm)],[c_18,c_134])).

tff(c_377,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_371,c_145])).

tff(c_316,plain,(
    ! [B_67,C_68,A_69] :
      ( k1_xboole_0 = B_67
      | v1_funct_2(C_68,A_69,B_67)
      | k1_relset_1(A_69,B_67,C_68) != A_69
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_431,plain,(
    ! [B_86,A_87,A_88] :
      ( k1_xboole_0 = B_86
      | v1_funct_2(A_87,A_88,B_86)
      | k1_relset_1(A_88,B_86,A_87) != A_88
      | ~ r1_tarski(A_87,k2_zfmisc_1(A_88,B_86)) ) ),
    inference(resolution,[status(thm)],[c_18,c_316])).

tff(c_437,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_371,c_431])).

tff(c_455,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_437])).

tff(c_456,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_455])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_485,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_8])).

tff(c_92,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_92])).

tff(c_118,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_118])).

tff(c_493,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_563,plain,(
    ! [C_100,A_101,B_102] :
      ( m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ r1_tarski(k2_relat_1(C_100),B_102)
      | ~ r1_tarski(k1_relat_1(C_100),A_101)
      | ~ v1_relat_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1399,plain,(
    ! [C_200,A_201,B_202] :
      ( r1_tarski(C_200,k2_zfmisc_1(A_201,B_202))
      | ~ r1_tarski(k2_relat_1(C_200),B_202)
      | ~ r1_tarski(k1_relat_1(C_200),A_201)
      | ~ v1_relat_1(C_200) ) ),
    inference(resolution,[status(thm)],[c_563,c_16])).

tff(c_1408,plain,(
    ! [C_203,A_204] :
      ( r1_tarski(C_203,k2_zfmisc_1(A_204,k2_relat_1(C_203)))
      | ~ r1_tarski(k1_relat_1(C_203),A_204)
      | ~ v1_relat_1(C_203) ) ),
    inference(resolution,[status(thm)],[c_6,c_1399])).

tff(c_1419,plain,(
    ! [A_204] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_204,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_204)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_1408])).

tff(c_1435,plain,(
    ! [A_206] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_206,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1419])).

tff(c_1445,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1435])).

tff(c_525,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_536,plain,(
    ! [A_92,B_93,A_6] :
      ( k1_relset_1(A_92,B_93,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_92,B_93)) ) ),
    inference(resolution,[status(thm)],[c_18,c_525])).

tff(c_1479,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1445,c_536])).

tff(c_1316,plain,(
    ! [B_185,C_186,A_187] :
      ( k1_xboole_0 = B_185
      | v1_funct_2(C_186,A_187,B_185)
      | k1_relset_1(A_187,B_185,C_186) != A_187
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_187,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1683,plain,(
    ! [B_230,A_231,A_232] :
      ( k1_xboole_0 = B_230
      | v1_funct_2(A_231,A_232,B_230)
      | k1_relset_1(A_232,B_230,A_231) != A_232
      | ~ r1_tarski(A_231,k2_zfmisc_1(A_232,B_230)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1316])).

tff(c_1689,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1445,c_1683])).

tff(c_1710,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_1689])).

tff(c_1711,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1710])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1393,plain,(
    ! [C_198,A_199] :
      ( m1_subset_1(C_198,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_198),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_198),A_199)
      | ~ v1_relat_1(C_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_563])).

tff(c_1395,plain,(
    ! [A_199] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_199)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_1393])).

tff(c_1397,plain,(
    ! [A_199] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1395])).

tff(c_1398,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1397])).

tff(c_1724,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1711,c_1398])).

tff(c_1750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1724])).

tff(c_1752,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1397])).

tff(c_104,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_1773,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1752,c_104])).

tff(c_1800,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1773,c_8])).

tff(c_734,plain,(
    ! [C_132,A_133,B_134] :
      ( r1_tarski(C_132,k2_zfmisc_1(A_133,B_134))
      | ~ r1_tarski(k2_relat_1(C_132),B_134)
      | ~ r1_tarski(k1_relat_1(C_132),A_133)
      | ~ v1_relat_1(C_132) ) ),
    inference(resolution,[status(thm)],[c_563,c_16])).

tff(c_743,plain,(
    ! [C_135,A_136] :
      ( r1_tarski(C_135,k2_zfmisc_1(A_136,k2_relat_1(C_135)))
      | ~ r1_tarski(k1_relat_1(C_135),A_136)
      | ~ v1_relat_1(C_135) ) ),
    inference(resolution,[status(thm)],[c_6,c_734])).

tff(c_754,plain,(
    ! [A_136] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_136,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_136)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_743])).

tff(c_765,plain,(
    ! [A_138] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_138,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_754])).

tff(c_775,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_765])).

tff(c_781,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_775,c_536])).

tff(c_711,plain,(
    ! [B_127,C_128,A_129] :
      ( k1_xboole_0 = B_127
      | v1_funct_2(C_128,A_129,B_127)
      | k1_relset_1(A_129,B_127,C_128) != A_129
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1012,plain,(
    ! [B_163,A_164,A_165] :
      ( k1_xboole_0 = B_163
      | v1_funct_2(A_164,A_165,B_163)
      | k1_relset_1(A_165,B_163,A_164) != A_165
      | ~ r1_tarski(A_164,k2_zfmisc_1(A_165,B_163)) ) ),
    inference(resolution,[status(thm)],[c_18,c_711])).

tff(c_1018,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_775,c_1012])).

tff(c_1039,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_1018])).

tff(c_1040,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1039])).

tff(c_728,plain,(
    ! [C_130,A_131] :
      ( m1_subset_1(C_130,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_130),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_130),A_131)
      | ~ v1_relat_1(C_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_563])).

tff(c_730,plain,(
    ! [A_131] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_131)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_728])).

tff(c_732,plain,(
    ! [A_131] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_730])).

tff(c_733,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_732])).

tff(c_1054,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_733])).

tff(c_1079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1054])).

tff(c_1081,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_1093,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1081,c_104])).

tff(c_612,plain,(
    ! [A_108,B_109,A_110] :
      ( k1_relset_1(A_108,B_109,A_110) = k1_relat_1(A_110)
      | ~ r1_tarski(A_110,k2_zfmisc_1(A_108,B_109)) ) ),
    inference(resolution,[status(thm)],[c_18,c_525])).

tff(c_628,plain,(
    ! [A_108,B_109] : k1_relset_1(A_108,B_109,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_612])).

tff(c_24,plain,(
    ! [A_14] :
      ( v1_funct_2(k1_xboole_0,A_14,k1_xboole_0)
      | k1_xboole_0 = A_14
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_14,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_47,plain,(
    ! [A_14] :
      ( v1_funct_2(k1_xboole_0,A_14,k1_xboole_0)
      | k1_xboole_0 = A_14
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24])).

tff(c_502,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_505,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_502])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_505])).

tff(c_511,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [C_16,B_15] :
      ( v1_funct_2(C_16,k1_xboole_0,B_15)
      | k1_relset_1(k1_xboole_0,B_15,C_16) != k1_xboole_0
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_638,plain,(
    ! [C_113,B_114] :
      ( v1_funct_2(C_113,k1_xboole_0,B_114)
      | k1_relset_1(k1_xboole_0,B_114,C_113) != k1_xboole_0
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_640,plain,(
    ! [B_114] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_114)
      | k1_relset_1(k1_xboole_0,B_114,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_511,c_638])).

tff(c_645,plain,(
    ! [B_114] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_114)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_640])).

tff(c_647,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_645])).

tff(c_1105,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_1093,c_647])).

tff(c_510,plain,(
    ! [A_14] :
      ( v1_funct_2(k1_xboole_0,A_14,k1_xboole_0)
      | k1_xboole_0 = A_14 ) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_1270,plain,(
    ! [A_179] :
      ( v1_funct_2('#skF_1',A_179,'#skF_1')
      | A_179 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_1093,c_1093,c_510])).

tff(c_1119,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_8])).

tff(c_1080,plain,(
    ! [A_131] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_131)
      | m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_1125,plain,(
    ! [A_131] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_131)
      | m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_1080])).

tff(c_1137,plain,(
    ! [A_167] : ~ r1_tarski(k1_relat_1('#skF_2'),A_167) ),
    inference(splitLeft,[status(thm)],[c_1125])).

tff(c_1142,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_1137])).

tff(c_1143,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1125])).

tff(c_1193,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_1143,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1195,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1193,c_2])).

tff(c_1198,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1119,c_1195])).

tff(c_1203,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_1198,c_80])).

tff(c_1273,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1270,c_1203])).

tff(c_1280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1105,c_1273])).

tff(c_1282,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_1786,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1773,c_1773,c_1282])).

tff(c_1751,plain,(
    ! [A_199] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_199)
      | m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_1397])).

tff(c_1949,plain,(
    ! [A_199] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_199)
      | m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1773,c_1751])).

tff(c_1951,plain,(
    ! [A_255] : ~ r1_tarski(k1_relat_1('#skF_2'),A_255) ),
    inference(splitLeft,[status(thm)],[c_1949])).

tff(c_1956,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_1951])).

tff(c_1957,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1949])).

tff(c_1961,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_1957,c_16])).

tff(c_1796,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1773,c_1773,c_104])).

tff(c_1967,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1961,c_1796])).

tff(c_1359,plain,(
    ! [C_192,B_193] :
      ( m1_subset_1(C_192,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_192),B_193)
      | ~ r1_tarski(k1_relat_1(C_192),k1_xboole_0)
      | ~ v1_relat_1(C_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_563])).

tff(c_1362,plain,(
    ! [B_193] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',B_193)
      | ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_1359])).

tff(c_1367,plain,(
    ! [B_193] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',B_193)
      | ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1362])).

tff(c_1392,plain,(
    ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1367])).

tff(c_1779,plain,(
    ~ r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1773,c_1392])).

tff(c_1975,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1967,c_1779])).

tff(c_1987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1800,c_1786,c_1975])).

tff(c_1989,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1367])).

tff(c_1368,plain,(
    ! [C_192] :
      ( m1_subset_1(C_192,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(C_192),k1_xboole_0)
      | ~ v1_relat_1(C_192) ) ),
    inference(resolution,[status(thm)],[c_6,c_1359])).

tff(c_1997,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1989,c_1368])).

tff(c_2009,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1997])).

tff(c_2047,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2009,c_16])).

tff(c_2061,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2047,c_104])).

tff(c_1281,plain,(
    ! [B_114] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_114) ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_2075,plain,(
    ! [B_114] : v1_funct_2('#skF_2','#skF_2',B_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2061,c_2061,c_1281])).

tff(c_2012,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1989,c_104])).

tff(c_2017,plain,(
    ~ v1_funct_2('#skF_2',k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_80])).

tff(c_2067,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2061,c_2017])).

tff(c_2179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2075,c_2067])).

tff(c_2180,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2265,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2259,c_2180])).

tff(c_2279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_38,c_2265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:59:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.66  
% 3.81/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.66  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.81/1.66  
% 3.81/1.66  %Foreground sorts:
% 3.81/1.66  
% 3.81/1.66  
% 3.81/1.66  %Background operators:
% 3.81/1.66  
% 3.81/1.66  
% 3.81/1.66  %Foreground operators:
% 3.81/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.81/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.81/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.81/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.81/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.81/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.81/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.81/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.81/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.81/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.81/1.66  
% 3.81/1.68  tff(f_86, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.81/1.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.81/1.68  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.81/1.68  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.81/1.68  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.81/1.68  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.81/1.68  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.81/1.68  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.81/1.68  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.81/1.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.68  tff(c_38, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.81/1.68  tff(c_2259, plain, (![C_275, A_276, B_277]: (m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))) | ~r1_tarski(k2_relat_1(C_275), B_277) | ~r1_tarski(k1_relat_1(C_275), A_276) | ~v1_relat_1(C_275))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.68  tff(c_40, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.81/1.68  tff(c_36, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.81/1.68  tff(c_44, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 3.81/1.68  tff(c_80, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 3.81/1.68  tff(c_231, plain, (![C_49, A_50, B_51]: (m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~r1_tarski(k2_relat_1(C_49), B_51) | ~r1_tarski(k1_relat_1(C_49), A_50) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.68  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.81/1.68  tff(c_346, plain, (![C_73, A_74, B_75]: (r1_tarski(C_73, k2_zfmisc_1(A_74, B_75)) | ~r1_tarski(k2_relat_1(C_73), B_75) | ~r1_tarski(k1_relat_1(C_73), A_74) | ~v1_relat_1(C_73))), inference(resolution, [status(thm)], [c_231, c_16])).
% 3.81/1.68  tff(c_348, plain, (![A_74]: (r1_tarski('#skF_2', k2_zfmisc_1(A_74, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_74) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_346])).
% 3.81/1.68  tff(c_366, plain, (![A_79]: (r1_tarski('#skF_2', k2_zfmisc_1(A_79, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_79))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_348])).
% 3.81/1.68  tff(c_371, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_366])).
% 3.81/1.68  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.81/1.68  tff(c_134, plain, (![A_30, B_31, C_32]: (k1_relset_1(A_30, B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.81/1.68  tff(c_145, plain, (![A_30, B_31, A_6]: (k1_relset_1(A_30, B_31, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_30, B_31)))), inference(resolution, [status(thm)], [c_18, c_134])).
% 3.81/1.68  tff(c_377, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_371, c_145])).
% 3.81/1.68  tff(c_316, plain, (![B_67, C_68, A_69]: (k1_xboole_0=B_67 | v1_funct_2(C_68, A_69, B_67) | k1_relset_1(A_69, B_67, C_68)!=A_69 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_67))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.81/1.68  tff(c_431, plain, (![B_86, A_87, A_88]: (k1_xboole_0=B_86 | v1_funct_2(A_87, A_88, B_86) | k1_relset_1(A_88, B_86, A_87)!=A_88 | ~r1_tarski(A_87, k2_zfmisc_1(A_88, B_86)))), inference(resolution, [status(thm)], [c_18, c_316])).
% 3.81/1.68  tff(c_437, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_371, c_431])).
% 3.81/1.68  tff(c_455, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_437])).
% 3.81/1.68  tff(c_456, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_80, c_455])).
% 3.81/1.68  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.81/1.68  tff(c_485, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_456, c_8])).
% 3.81/1.68  tff(c_92, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.68  tff(c_99, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_92])).
% 3.81/1.68  tff(c_118, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_99])).
% 3.81/1.68  tff(c_492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_485, c_118])).
% 3.81/1.68  tff(c_493, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_99])).
% 3.81/1.68  tff(c_563, plain, (![C_100, A_101, B_102]: (m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~r1_tarski(k2_relat_1(C_100), B_102) | ~r1_tarski(k1_relat_1(C_100), A_101) | ~v1_relat_1(C_100))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.68  tff(c_1399, plain, (![C_200, A_201, B_202]: (r1_tarski(C_200, k2_zfmisc_1(A_201, B_202)) | ~r1_tarski(k2_relat_1(C_200), B_202) | ~r1_tarski(k1_relat_1(C_200), A_201) | ~v1_relat_1(C_200))), inference(resolution, [status(thm)], [c_563, c_16])).
% 3.81/1.68  tff(c_1408, plain, (![C_203, A_204]: (r1_tarski(C_203, k2_zfmisc_1(A_204, k2_relat_1(C_203))) | ~r1_tarski(k1_relat_1(C_203), A_204) | ~v1_relat_1(C_203))), inference(resolution, [status(thm)], [c_6, c_1399])).
% 3.81/1.68  tff(c_1419, plain, (![A_204]: (r1_tarski('#skF_2', k2_zfmisc_1(A_204, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_204) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_1408])).
% 3.81/1.68  tff(c_1435, plain, (![A_206]: (r1_tarski('#skF_2', k2_zfmisc_1(A_206, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_206))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1419])).
% 3.81/1.68  tff(c_1445, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1435])).
% 3.81/1.68  tff(c_525, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.81/1.68  tff(c_536, plain, (![A_92, B_93, A_6]: (k1_relset_1(A_92, B_93, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_92, B_93)))), inference(resolution, [status(thm)], [c_18, c_525])).
% 3.81/1.68  tff(c_1479, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1445, c_536])).
% 3.81/1.68  tff(c_1316, plain, (![B_185, C_186, A_187]: (k1_xboole_0=B_185 | v1_funct_2(C_186, A_187, B_185) | k1_relset_1(A_187, B_185, C_186)!=A_187 | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_187, B_185))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.81/1.68  tff(c_1683, plain, (![B_230, A_231, A_232]: (k1_xboole_0=B_230 | v1_funct_2(A_231, A_232, B_230) | k1_relset_1(A_232, B_230, A_231)!=A_232 | ~r1_tarski(A_231, k2_zfmisc_1(A_232, B_230)))), inference(resolution, [status(thm)], [c_18, c_1316])).
% 3.81/1.68  tff(c_1689, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1445, c_1683])).
% 3.81/1.69  tff(c_1710, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_1689])).
% 3.81/1.69  tff(c_1711, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_80, c_1710])).
% 3.81/1.69  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.81/1.69  tff(c_1393, plain, (![C_198, A_199]: (m1_subset_1(C_198, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_198), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_198), A_199) | ~v1_relat_1(C_198))), inference(superposition, [status(thm), theory('equality')], [c_12, c_563])).
% 3.81/1.69  tff(c_1395, plain, (![A_199]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_199) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_1393])).
% 3.81/1.69  tff(c_1397, plain, (![A_199]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_199))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1395])).
% 3.81/1.69  tff(c_1398, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1397])).
% 3.81/1.69  tff(c_1724, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1711, c_1398])).
% 3.81/1.69  tff(c_1750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1724])).
% 3.81/1.69  tff(c_1752, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1397])).
% 3.81/1.69  tff(c_104, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_92])).
% 3.81/1.69  tff(c_1773, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1752, c_104])).
% 3.81/1.69  tff(c_1800, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1773, c_8])).
% 3.81/1.69  tff(c_734, plain, (![C_132, A_133, B_134]: (r1_tarski(C_132, k2_zfmisc_1(A_133, B_134)) | ~r1_tarski(k2_relat_1(C_132), B_134) | ~r1_tarski(k1_relat_1(C_132), A_133) | ~v1_relat_1(C_132))), inference(resolution, [status(thm)], [c_563, c_16])).
% 3.81/1.69  tff(c_743, plain, (![C_135, A_136]: (r1_tarski(C_135, k2_zfmisc_1(A_136, k2_relat_1(C_135))) | ~r1_tarski(k1_relat_1(C_135), A_136) | ~v1_relat_1(C_135))), inference(resolution, [status(thm)], [c_6, c_734])).
% 3.81/1.69  tff(c_754, plain, (![A_136]: (r1_tarski('#skF_2', k2_zfmisc_1(A_136, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_136) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_743])).
% 3.81/1.69  tff(c_765, plain, (![A_138]: (r1_tarski('#skF_2', k2_zfmisc_1(A_138, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_138))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_754])).
% 3.81/1.69  tff(c_775, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_765])).
% 3.81/1.69  tff(c_781, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_775, c_536])).
% 3.81/1.69  tff(c_711, plain, (![B_127, C_128, A_129]: (k1_xboole_0=B_127 | v1_funct_2(C_128, A_129, B_127) | k1_relset_1(A_129, B_127, C_128)!=A_129 | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_127))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.81/1.69  tff(c_1012, plain, (![B_163, A_164, A_165]: (k1_xboole_0=B_163 | v1_funct_2(A_164, A_165, B_163) | k1_relset_1(A_165, B_163, A_164)!=A_165 | ~r1_tarski(A_164, k2_zfmisc_1(A_165, B_163)))), inference(resolution, [status(thm)], [c_18, c_711])).
% 3.81/1.69  tff(c_1018, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_775, c_1012])).
% 3.81/1.69  tff(c_1039, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_781, c_1018])).
% 3.81/1.69  tff(c_1040, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_80, c_1039])).
% 3.81/1.69  tff(c_728, plain, (![C_130, A_131]: (m1_subset_1(C_130, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_130), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_130), A_131) | ~v1_relat_1(C_130))), inference(superposition, [status(thm), theory('equality')], [c_12, c_563])).
% 3.81/1.69  tff(c_730, plain, (![A_131]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_131) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_728])).
% 3.81/1.69  tff(c_732, plain, (![A_131]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_131))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_730])).
% 3.81/1.69  tff(c_733, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_732])).
% 3.81/1.69  tff(c_1054, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_733])).
% 3.81/1.69  tff(c_1079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1054])).
% 3.81/1.69  tff(c_1081, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_732])).
% 3.81/1.69  tff(c_1093, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1081, c_104])).
% 3.81/1.69  tff(c_612, plain, (![A_108, B_109, A_110]: (k1_relset_1(A_108, B_109, A_110)=k1_relat_1(A_110) | ~r1_tarski(A_110, k2_zfmisc_1(A_108, B_109)))), inference(resolution, [status(thm)], [c_18, c_525])).
% 3.81/1.69  tff(c_628, plain, (![A_108, B_109]: (k1_relset_1(A_108, B_109, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_612])).
% 3.81/1.69  tff(c_24, plain, (![A_14]: (v1_funct_2(k1_xboole_0, A_14, k1_xboole_0) | k1_xboole_0=A_14 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_14, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.81/1.69  tff(c_47, plain, (![A_14]: (v1_funct_2(k1_xboole_0, A_14, k1_xboole_0) | k1_xboole_0=A_14 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_24])).
% 3.81/1.69  tff(c_502, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_47])).
% 3.81/1.69  tff(c_505, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_502])).
% 3.81/1.69  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_505])).
% 3.81/1.69  tff(c_511, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_47])).
% 3.81/1.69  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.81/1.69  tff(c_28, plain, (![C_16, B_15]: (v1_funct_2(C_16, k1_xboole_0, B_15) | k1_relset_1(k1_xboole_0, B_15, C_16)!=k1_xboole_0 | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_15))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.81/1.69  tff(c_638, plain, (![C_113, B_114]: (v1_funct_2(C_113, k1_xboole_0, B_114) | k1_relset_1(k1_xboole_0, B_114, C_113)!=k1_xboole_0 | ~m1_subset_1(C_113, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 3.81/1.69  tff(c_640, plain, (![B_114]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_114) | k1_relset_1(k1_xboole_0, B_114, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_511, c_638])).
% 3.81/1.69  tff(c_645, plain, (![B_114]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_114) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_628, c_640])).
% 3.81/1.69  tff(c_647, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_645])).
% 3.81/1.69  tff(c_1105, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_1093, c_647])).
% 3.81/1.69  tff(c_510, plain, (![A_14]: (v1_funct_2(k1_xboole_0, A_14, k1_xboole_0) | k1_xboole_0=A_14)), inference(splitRight, [status(thm)], [c_47])).
% 3.81/1.69  tff(c_1270, plain, (![A_179]: (v1_funct_2('#skF_1', A_179, '#skF_1') | A_179='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_1093, c_1093, c_510])).
% 3.81/1.69  tff(c_1119, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_8])).
% 3.81/1.69  tff(c_1080, plain, (![A_131]: (~r1_tarski(k1_relat_1('#skF_2'), A_131) | m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_732])).
% 3.81/1.69  tff(c_1125, plain, (![A_131]: (~r1_tarski(k1_relat_1('#skF_2'), A_131) | m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_1080])).
% 3.81/1.69  tff(c_1137, plain, (![A_167]: (~r1_tarski(k1_relat_1('#skF_2'), A_167))), inference(splitLeft, [status(thm)], [c_1125])).
% 3.81/1.69  tff(c_1142, plain, $false, inference(resolution, [status(thm)], [c_6, c_1137])).
% 3.81/1.69  tff(c_1143, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1125])).
% 3.81/1.69  tff(c_1193, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_1143, c_16])).
% 3.81/1.69  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.69  tff(c_1195, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1193, c_2])).
% 3.81/1.69  tff(c_1198, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1119, c_1195])).
% 3.81/1.69  tff(c_1203, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_1198, c_80])).
% 3.81/1.69  tff(c_1273, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1270, c_1203])).
% 3.81/1.69  tff(c_1280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1105, c_1273])).
% 3.81/1.69  tff(c_1282, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_645])).
% 3.81/1.69  tff(c_1786, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1773, c_1773, c_1282])).
% 3.81/1.69  tff(c_1751, plain, (![A_199]: (~r1_tarski(k1_relat_1('#skF_2'), A_199) | m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_1397])).
% 3.81/1.69  tff(c_1949, plain, (![A_199]: (~r1_tarski(k1_relat_1('#skF_2'), A_199) | m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1773, c_1751])).
% 3.81/1.69  tff(c_1951, plain, (![A_255]: (~r1_tarski(k1_relat_1('#skF_2'), A_255))), inference(splitLeft, [status(thm)], [c_1949])).
% 3.81/1.69  tff(c_1956, plain, $false, inference(resolution, [status(thm)], [c_6, c_1951])).
% 3.81/1.69  tff(c_1957, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1949])).
% 3.81/1.69  tff(c_1961, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_1957, c_16])).
% 3.81/1.69  tff(c_1796, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1773, c_1773, c_104])).
% 3.81/1.69  tff(c_1967, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_1961, c_1796])).
% 3.81/1.69  tff(c_1359, plain, (![C_192, B_193]: (m1_subset_1(C_192, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_192), B_193) | ~r1_tarski(k1_relat_1(C_192), k1_xboole_0) | ~v1_relat_1(C_192))), inference(superposition, [status(thm), theory('equality')], [c_14, c_563])).
% 3.81/1.69  tff(c_1362, plain, (![B_193]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', B_193) | ~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_1359])).
% 3.81/1.69  tff(c_1367, plain, (![B_193]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', B_193) | ~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1362])).
% 3.81/1.69  tff(c_1392, plain, (~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1367])).
% 3.81/1.69  tff(c_1779, plain, (~r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1773, c_1392])).
% 3.81/1.69  tff(c_1975, plain, (~r1_tarski(k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1967, c_1779])).
% 3.81/1.69  tff(c_1987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1800, c_1786, c_1975])).
% 3.81/1.69  tff(c_1989, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1367])).
% 3.81/1.69  tff(c_1368, plain, (![C_192]: (m1_subset_1(C_192, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(C_192), k1_xboole_0) | ~v1_relat_1(C_192))), inference(resolution, [status(thm)], [c_6, c_1359])).
% 3.81/1.69  tff(c_1997, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1989, c_1368])).
% 3.81/1.69  tff(c_2009, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1997])).
% 3.81/1.69  tff(c_2047, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_2009, c_16])).
% 3.81/1.69  tff(c_2061, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2047, c_104])).
% 3.81/1.69  tff(c_1281, plain, (![B_114]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_114))), inference(splitRight, [status(thm)], [c_645])).
% 3.81/1.69  tff(c_2075, plain, (![B_114]: (v1_funct_2('#skF_2', '#skF_2', B_114))), inference(demodulation, [status(thm), theory('equality')], [c_2061, c_2061, c_1281])).
% 3.81/1.69  tff(c_2012, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1989, c_104])).
% 3.81/1.69  tff(c_2017, plain, (~v1_funct_2('#skF_2', k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_80])).
% 3.81/1.69  tff(c_2067, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2061, c_2017])).
% 3.81/1.69  tff(c_2179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2075, c_2067])).
% 3.81/1.69  tff(c_2180, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_44])).
% 3.81/1.69  tff(c_2265, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2259, c_2180])).
% 3.81/1.69  tff(c_2279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_38, c_2265])).
% 3.81/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.69  
% 3.81/1.69  Inference rules
% 3.81/1.69  ----------------------
% 3.81/1.69  #Ref     : 0
% 3.81/1.69  #Sup     : 439
% 3.81/1.69  #Fact    : 0
% 3.81/1.69  #Define  : 0
% 3.81/1.69  #Split   : 19
% 3.81/1.69  #Chain   : 0
% 3.81/1.69  #Close   : 0
% 3.81/1.69  
% 3.81/1.69  Ordering : KBO
% 3.81/1.69  
% 3.81/1.69  Simplification rules
% 3.81/1.69  ----------------------
% 3.81/1.69  #Subsume      : 38
% 3.81/1.69  #Demod        : 617
% 3.81/1.69  #Tautology    : 211
% 3.81/1.69  #SimpNegUnit  : 9
% 3.81/1.69  #BackRed      : 180
% 3.81/1.69  
% 3.81/1.69  #Partial instantiations: 0
% 3.81/1.69  #Strategies tried      : 1
% 3.81/1.69  
% 3.81/1.69  Timing (in seconds)
% 3.81/1.69  ----------------------
% 3.81/1.69  Preprocessing        : 0.30
% 3.81/1.69  Parsing              : 0.16
% 3.81/1.69  CNF conversion       : 0.02
% 3.81/1.69  Main loop            : 0.58
% 3.81/1.69  Inferencing          : 0.20
% 3.81/1.69  Reduction            : 0.19
% 3.81/1.69  Demodulation         : 0.13
% 3.81/1.69  BG Simplification    : 0.03
% 3.81/1.69  Subsumption          : 0.12
% 3.81/1.69  Abstraction          : 0.03
% 3.81/1.69  MUC search           : 0.00
% 3.81/1.69  Cooper               : 0.00
% 3.81/1.69  Total                : 0.94
% 3.81/1.69  Index Insertion      : 0.00
% 3.81/1.69  Index Deletion       : 0.00
% 3.81/1.69  Index Matching       : 0.00
% 3.81/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
