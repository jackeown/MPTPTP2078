%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:22 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 288 expanded)
%              Number of leaves         :   33 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  155 ( 590 expanded)
%              Number of equality atoms :   31 (  91 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_723,plain,(
    ! [A_174,B_175,C_176] :
      ( k2_relset_1(A_174,B_175,C_176) = k2_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_732,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_723])).

tff(c_34,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_733,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_34])).

tff(c_93,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_102,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_93])).

tff(c_130,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_139,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_130])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_262,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_relset_1(A_97,B_98,C_99) = k1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_276,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_262])).

tff(c_18,plain,(
    ! [A_13] :
      ( v1_xboole_0(k2_relat_1(A_13))
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,(
    ! [A_42] :
      ( v1_xboole_0(k2_relat_1(A_42))
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_43] :
      ( k2_relat_1(A_43) = k1_xboole_0
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_43,c_6])).

tff(c_64,plain,(
    ! [A_46] :
      ( k2_relat_1(k2_relat_1(A_46)) = k1_xboole_0
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_73,plain,(
    ! [A_46] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_46))
      | ~ v1_xboole_0(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_18])).

tff(c_111,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(k2_relat_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_118,plain,(
    ! [A_13] : ~ v1_xboole_0(A_13) ),
    inference(resolution,[status(thm)],[c_18,c_111])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_182,plain,(
    ! [A_77,C_78,B_79] :
      ( m1_subset_1(A_77,C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_190,plain,(
    ! [A_81,B_82,A_83] :
      ( m1_subset_1(A_81,B_82)
      | ~ r2_hidden(A_81,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_10,c_182])).

tff(c_194,plain,(
    ! [A_84,B_85] :
      ( m1_subset_1('#skF_1'(A_84),B_85)
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_120,c_190])).

tff(c_58,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_45,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_63,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_110,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_220,plain,(
    ~ r1_tarski(k1_relset_1('#skF_3','#skF_2','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_110])).

tff(c_277,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_220])).

tff(c_286,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_277])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_139,c_286])).

tff(c_291,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_300,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_291,c_6])).

tff(c_302,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_291])).

tff(c_47,plain,(
    ! [A_42] :
      ( k2_relat_1(A_42) = k1_xboole_0
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_43,c_6])).

tff(c_314,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_302,c_47])).

tff(c_331,plain,(
    ! [A_100] :
      ( ~ v1_xboole_0(k2_relat_1(A_100))
      | ~ v1_xboole_0(A_100) ) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_334,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_331])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_302,c_334])).

tff(c_344,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_482,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_496,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_482])).

tff(c_497,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_34])).

tff(c_387,plain,(
    ! [C_107,A_108,B_109] :
      ( v4_relat_1(C_107,A_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_396,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_387])).

tff(c_532,plain,(
    ! [A_146,B_147,C_148] :
      ( k1_relset_1(A_146,B_147,C_148) = k1_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_546,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_532])).

tff(c_424,plain,(
    ! [A_117,C_118,B_119] :
      ( m1_subset_1(A_117,C_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(C_118))
      | ~ r2_hidden(A_117,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_432,plain,(
    ! [A_121,B_122,A_123] :
      ( m1_subset_1(A_121,B_122)
      | ~ r2_hidden(A_121,A_123)
      | ~ r1_tarski(A_123,B_122) ) ),
    inference(resolution,[status(thm)],[c_10,c_424])).

tff(c_436,plain,(
    ! [A_124,B_125] :
      ( m1_subset_1('#skF_1'(A_124),B_125)
      | ~ r1_tarski(A_124,B_125)
      | v1_xboole_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_4,c_432])).

tff(c_378,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_461,plain,
    ( ~ r1_tarski(k1_relset_1('#skF_3','#skF_2','#skF_4'),'#skF_3')
    | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_436,c_378])).

tff(c_518,plain,(
    ~ r1_tarski(k1_relset_1('#skF_3','#skF_2','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_547,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_518])).

tff(c_556,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_547])).

tff(c_560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_396,c_556])).

tff(c_561,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_570,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_561,c_6])).

tff(c_594,plain,(
    ! [A_150,B_151,C_152] :
      ( k1_relset_1(A_150,B_151,C_152) = k1_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_605,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_594])).

tff(c_609,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_605])).

tff(c_20,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(k1_relat_1(A_14))
      | ~ v1_relat_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_619,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_20])).

tff(c_627,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_344,c_619])).

tff(c_631,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_627,c_47])).

tff(c_638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_631])).

tff(c_639,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_648,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_639,c_6])).

tff(c_768,plain,(
    ! [A_179,B_180,C_181] :
      ( k1_relset_1(A_179,B_180,C_181) = k1_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_779,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_768])).

tff(c_783,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_779])).

tff(c_793,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_20])).

tff(c_801,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_344,c_793])).

tff(c_805,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_801,c_47])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_733,c_805])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.41  
% 2.70/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.41  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.70/1.41  
% 2.70/1.41  %Foreground sorts:
% 2.70/1.41  
% 2.70/1.41  
% 2.70/1.41  %Background operators:
% 2.70/1.41  
% 2.70/1.41  
% 2.70/1.41  %Foreground operators:
% 2.70/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.70/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.70/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.70/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.70/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.41  
% 2.70/1.43  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.70/1.43  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.70/1.43  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.70/1.43  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.70/1.43  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.70/1.43  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.70/1.43  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 2.70/1.43  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.70/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.70/1.43  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.70/1.43  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.70/1.43  tff(f_63, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.70/1.43  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.70/1.43  tff(c_723, plain, (![A_174, B_175, C_176]: (k2_relset_1(A_174, B_175, C_176)=k2_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.70/1.43  tff(c_732, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_723])).
% 2.70/1.43  tff(c_34, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.70/1.43  tff(c_733, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_732, c_34])).
% 2.70/1.43  tff(c_93, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.70/1.43  tff(c_102, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_93])).
% 2.70/1.43  tff(c_130, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.70/1.43  tff(c_139, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_130])).
% 2.70/1.43  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.70/1.43  tff(c_262, plain, (![A_97, B_98, C_99]: (k1_relset_1(A_97, B_98, C_99)=k1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.43  tff(c_276, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_262])).
% 2.70/1.43  tff(c_18, plain, (![A_13]: (v1_xboole_0(k2_relat_1(A_13)) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.70/1.43  tff(c_43, plain, (![A_42]: (v1_xboole_0(k2_relat_1(A_42)) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.70/1.43  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.43  tff(c_48, plain, (![A_43]: (k2_relat_1(A_43)=k1_xboole_0 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_43, c_6])).
% 2.70/1.43  tff(c_64, plain, (![A_46]: (k2_relat_1(k2_relat_1(A_46))=k1_xboole_0 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_18, c_48])).
% 2.70/1.43  tff(c_73, plain, (![A_46]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_46)) | ~v1_xboole_0(A_46))), inference(superposition, [status(thm), theory('equality')], [c_64, c_18])).
% 2.70/1.43  tff(c_111, plain, (![A_58]: (~v1_xboole_0(k2_relat_1(A_58)) | ~v1_xboole_0(A_58))), inference(splitLeft, [status(thm)], [c_73])).
% 2.70/1.43  tff(c_118, plain, (![A_13]: (~v1_xboole_0(A_13))), inference(resolution, [status(thm)], [c_18, c_111])).
% 2.70/1.43  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.43  tff(c_120, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_118, c_4])).
% 2.70/1.43  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.43  tff(c_182, plain, (![A_77, C_78, B_79]: (m1_subset_1(A_77, C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.43  tff(c_190, plain, (![A_81, B_82, A_83]: (m1_subset_1(A_81, B_82) | ~r2_hidden(A_81, A_83) | ~r1_tarski(A_83, B_82))), inference(resolution, [status(thm)], [c_10, c_182])).
% 2.70/1.43  tff(c_194, plain, (![A_84, B_85]: (m1_subset_1('#skF_1'(A_84), B_85) | ~r1_tarski(A_84, B_85))), inference(resolution, [status(thm)], [c_120, c_190])).
% 2.70/1.43  tff(c_58, plain, (![D_45]: (~r2_hidden(D_45, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_45, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.70/1.43  tff(c_63, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.70/1.43  tff(c_110, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_63])).
% 2.70/1.43  tff(c_220, plain, (~r1_tarski(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_194, c_110])).
% 2.70/1.43  tff(c_277, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_220])).
% 2.70/1.43  tff(c_286, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_277])).
% 2.70/1.43  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_139, c_286])).
% 2.70/1.43  tff(c_291, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_63])).
% 2.70/1.43  tff(c_300, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_291, c_6])).
% 2.70/1.43  tff(c_302, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_300, c_291])).
% 2.70/1.43  tff(c_47, plain, (![A_42]: (k2_relat_1(A_42)=k1_xboole_0 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_43, c_6])).
% 2.70/1.43  tff(c_314, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_302, c_47])).
% 2.70/1.43  tff(c_331, plain, (![A_100]: (~v1_xboole_0(k2_relat_1(A_100)) | ~v1_xboole_0(A_100))), inference(splitLeft, [status(thm)], [c_73])).
% 2.70/1.43  tff(c_334, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_314, c_331])).
% 2.70/1.43  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_302, c_302, c_334])).
% 2.70/1.43  tff(c_344, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_73])).
% 2.70/1.43  tff(c_482, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.70/1.43  tff(c_496, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_482])).
% 2.70/1.43  tff(c_497, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_496, c_34])).
% 2.70/1.43  tff(c_387, plain, (![C_107, A_108, B_109]: (v4_relat_1(C_107, A_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.70/1.43  tff(c_396, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_387])).
% 2.70/1.43  tff(c_532, plain, (![A_146, B_147, C_148]: (k1_relset_1(A_146, B_147, C_148)=k1_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.43  tff(c_546, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_532])).
% 2.70/1.43  tff(c_424, plain, (![A_117, C_118, B_119]: (m1_subset_1(A_117, C_118) | ~m1_subset_1(B_119, k1_zfmisc_1(C_118)) | ~r2_hidden(A_117, B_119))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.43  tff(c_432, plain, (![A_121, B_122, A_123]: (m1_subset_1(A_121, B_122) | ~r2_hidden(A_121, A_123) | ~r1_tarski(A_123, B_122))), inference(resolution, [status(thm)], [c_10, c_424])).
% 2.70/1.43  tff(c_436, plain, (![A_124, B_125]: (m1_subset_1('#skF_1'(A_124), B_125) | ~r1_tarski(A_124, B_125) | v1_xboole_0(A_124))), inference(resolution, [status(thm)], [c_4, c_432])).
% 2.70/1.43  tff(c_378, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_63])).
% 2.70/1.43  tff(c_461, plain, (~r1_tarski(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_436, c_378])).
% 2.70/1.43  tff(c_518, plain, (~r1_tarski(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_461])).
% 2.70/1.43  tff(c_547, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_518])).
% 2.70/1.43  tff(c_556, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_547])).
% 2.70/1.43  tff(c_560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_396, c_556])).
% 2.70/1.43  tff(c_561, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_461])).
% 2.70/1.43  tff(c_570, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_561, c_6])).
% 2.70/1.43  tff(c_594, plain, (![A_150, B_151, C_152]: (k1_relset_1(A_150, B_151, C_152)=k1_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.43  tff(c_605, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_594])).
% 2.70/1.43  tff(c_609, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_570, c_605])).
% 2.70/1.43  tff(c_20, plain, (![A_14]: (~v1_xboole_0(k1_relat_1(A_14)) | ~v1_relat_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.43  tff(c_619, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_609, c_20])).
% 2.70/1.43  tff(c_627, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_344, c_619])).
% 2.70/1.43  tff(c_631, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_627, c_47])).
% 2.70/1.43  tff(c_638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_497, c_631])).
% 2.70/1.43  tff(c_639, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_63])).
% 2.70/1.43  tff(c_648, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_639, c_6])).
% 2.70/1.43  tff(c_768, plain, (![A_179, B_180, C_181]: (k1_relset_1(A_179, B_180, C_181)=k1_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.43  tff(c_779, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_768])).
% 2.70/1.43  tff(c_783, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_648, c_779])).
% 2.70/1.43  tff(c_793, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_783, c_20])).
% 2.70/1.43  tff(c_801, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_344, c_793])).
% 2.70/1.43  tff(c_805, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_801, c_47])).
% 2.70/1.43  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_733, c_805])).
% 2.70/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.43  
% 2.70/1.43  Inference rules
% 2.70/1.43  ----------------------
% 2.70/1.43  #Ref     : 0
% 2.70/1.43  #Sup     : 158
% 2.70/1.43  #Fact    : 0
% 2.70/1.43  #Define  : 0
% 2.70/1.43  #Split   : 4
% 2.70/1.43  #Chain   : 0
% 2.70/1.43  #Close   : 0
% 2.70/1.43  
% 2.70/1.43  Ordering : KBO
% 2.70/1.43  
% 2.70/1.43  Simplification rules
% 2.70/1.43  ----------------------
% 2.70/1.43  #Subsume      : 16
% 2.70/1.43  #Demod        : 65
% 2.70/1.43  #Tautology    : 53
% 2.70/1.43  #SimpNegUnit  : 5
% 2.70/1.43  #BackRed      : 19
% 2.70/1.43  
% 2.70/1.43  #Partial instantiations: 0
% 2.70/1.43  #Strategies tried      : 1
% 2.70/1.43  
% 2.70/1.43  Timing (in seconds)
% 2.70/1.43  ----------------------
% 2.70/1.43  Preprocessing        : 0.32
% 2.70/1.43  Parsing              : 0.17
% 2.70/1.43  CNF conversion       : 0.02
% 2.70/1.43  Main loop            : 0.34
% 2.70/1.43  Inferencing          : 0.14
% 2.70/1.43  Reduction            : 0.10
% 2.70/1.43  Demodulation         : 0.06
% 2.70/1.43  BG Simplification    : 0.02
% 2.70/1.43  Subsumption          : 0.06
% 2.70/1.43  Abstraction          : 0.02
% 2.70/1.43  MUC search           : 0.00
% 2.70/1.43  Cooper               : 0.00
% 2.70/1.43  Total                : 0.70
% 2.70/1.43  Index Insertion      : 0.00
% 2.70/1.43  Index Deletion       : 0.00
% 2.70/1.43  Index Matching       : 0.00
% 2.70/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
