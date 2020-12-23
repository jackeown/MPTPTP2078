%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:09 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 221 expanded)
%              Number of leaves         :   34 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  147 ( 442 expanded)
%              Number of equality atoms :   25 (  64 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_881,plain,(
    ! [A_195,B_196,C_197] :
      ( k1_relset_1(A_195,B_196,C_197) = k1_relat_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_895,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_881])).

tff(c_36,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_896,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_36])).

tff(c_777,plain,(
    ! [C_169,A_170,B_171] :
      ( v1_relat_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_786,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_777])).

tff(c_133,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_142,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_133])).

tff(c_232,plain,(
    ! [C_90,B_91,A_92] :
      ( v5_relat_1(C_90,B_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_251,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_232])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_252,plain,(
    ! [A_93,B_94,C_95] :
      ( k2_relset_1(A_93,B_94,C_95) = k2_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_271,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_252])).

tff(c_20,plain,(
    ! [A_15] :
      ( v1_xboole_0(k1_relat_1(A_15))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_45,plain,(
    ! [A_44] :
      ( v1_xboole_0(k1_relat_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    ! [A_45] :
      ( k1_relat_1(A_45) = k1_xboole_0
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_45,c_12])).

tff(c_72,plain,(
    ! [A_51] :
      ( k1_relat_1(k1_relat_1(A_51)) = k1_xboole_0
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_20,c_50])).

tff(c_81,plain,(
    ! [A_51] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_51))
      | ~ v1_xboole_0(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_20])).

tff(c_107,plain,(
    ! [A_57] :
      ( ~ v1_xboole_0(k1_relat_1(A_57))
      | ~ v1_xboole_0(A_57) ) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_114,plain,(
    ! [A_15] : ~ v1_xboole_0(A_15) ),
    inference(resolution,[status(thm)],[c_20,c_107])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_4])).

tff(c_165,plain,(
    ! [C_75,B_76,A_77] :
      ( r2_hidden(C_75,B_76)
      | ~ r2_hidden(C_75,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_187,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81),B_82)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_117,c_165])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_207,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1('#skF_1'(A_86),B_87)
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_187,c_14])).

tff(c_57,plain,(
    ! [A_49] :
      ( v1_xboole_0(A_49)
      | r2_hidden('#skF_1'(A_49),A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [D_40] :
      ( ~ r2_hidden(D_40,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_40,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_57,c_34])).

tff(c_120,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_68])).

tff(c_221,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_207,c_120])).

tff(c_272,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_221])).

tff(c_283,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_272])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_251,c_283])).

tff(c_288,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_468,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_487,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_468])).

tff(c_488,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_36])).

tff(c_313,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_322,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_313])).

tff(c_354,plain,(
    ! [C_109,B_110,A_111] :
      ( v5_relat_1(C_109,B_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_368,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_354])).

tff(c_387,plain,(
    ! [C_119,B_120,A_121] :
      ( r2_hidden(C_119,B_120)
      | ~ r2_hidden(C_119,A_121)
      | ~ r1_tarski(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_409,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_1'(A_125),B_126)
      | ~ r1_tarski(A_125,B_126)
      | v1_xboole_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_4,c_387])).

tff(c_424,plain,(
    ! [A_125,B_126] :
      ( m1_subset_1('#skF_1'(A_125),B_126)
      | ~ r1_tarski(A_125,B_126)
      | v1_xboole_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_409,c_14])).

tff(c_593,plain,(
    ! [A_154,B_155,C_156] :
      ( k2_relset_1(A_154,B_155,C_156) = k2_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_617,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_593])).

tff(c_298,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_620,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_298])).

tff(c_629,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_424,c_620])).

tff(c_666,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_629])).

tff(c_669,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_666])).

tff(c_676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_368,c_669])).

tff(c_677,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_629])).

tff(c_22,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(k2_relat_1(A_16))
      | ~ v1_relat_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_683,plain,
    ( ~ v1_relat_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_677,c_22])).

tff(c_695,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_683])).

tff(c_49,plain,(
    ! [A_44] :
      ( k1_relat_1(A_44) = k1_xboole_0
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_45,c_12])).

tff(c_706,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_695,c_49])).

tff(c_713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_706])).

tff(c_714,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_737,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_714,c_12])).

tff(c_1003,plain,(
    ! [A_210,B_211,C_212] :
      ( k2_relset_1(A_210,B_211,C_212) = k2_relat_1(C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1018,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_1003])).

tff(c_1023,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_1018])).

tff(c_1038,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1023,c_22])).

tff(c_1050,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_288,c_1038])).

tff(c_1054,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1050,c_49])).

tff(c_1061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_896,c_1054])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.75  
% 3.36/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.75  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.36/1.75  
% 3.36/1.75  %Foreground sorts:
% 3.36/1.75  
% 3.36/1.75  
% 3.36/1.75  %Background operators:
% 3.36/1.75  
% 3.36/1.75  
% 3.36/1.75  %Foreground operators:
% 3.36/1.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.36/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.36/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.75  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.36/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.36/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.36/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.36/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.36/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.75  
% 3.36/1.78  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.36/1.78  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.36/1.78  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.36/1.78  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.36/1.78  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.36/1.78  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.36/1.78  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.36/1.78  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.36/1.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.36/1.78  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.36/1.78  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.36/1.78  tff(f_64, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.36/1.78  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.78  tff(c_881, plain, (![A_195, B_196, C_197]: (k1_relset_1(A_195, B_196, C_197)=k1_relat_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.36/1.78  tff(c_895, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_881])).
% 3.36/1.78  tff(c_36, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.78  tff(c_896, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_895, c_36])).
% 3.36/1.78  tff(c_777, plain, (![C_169, A_170, B_171]: (v1_relat_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.36/1.78  tff(c_786, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_777])).
% 3.36/1.78  tff(c_133, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.36/1.78  tff(c_142, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_133])).
% 3.36/1.78  tff(c_232, plain, (![C_90, B_91, A_92]: (v5_relat_1(C_90, B_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.78  tff(c_251, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_232])).
% 3.36/1.78  tff(c_18, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.36/1.78  tff(c_252, plain, (![A_93, B_94, C_95]: (k2_relset_1(A_93, B_94, C_95)=k2_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.36/1.78  tff(c_271, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_252])).
% 3.36/1.78  tff(c_20, plain, (![A_15]: (v1_xboole_0(k1_relat_1(A_15)) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.36/1.78  tff(c_45, plain, (![A_44]: (v1_xboole_0(k1_relat_1(A_44)) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.36/1.78  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.36/1.78  tff(c_50, plain, (![A_45]: (k1_relat_1(A_45)=k1_xboole_0 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_45, c_12])).
% 3.36/1.78  tff(c_72, plain, (![A_51]: (k1_relat_1(k1_relat_1(A_51))=k1_xboole_0 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_20, c_50])).
% 3.36/1.78  tff(c_81, plain, (![A_51]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_51)) | ~v1_xboole_0(A_51))), inference(superposition, [status(thm), theory('equality')], [c_72, c_20])).
% 3.36/1.78  tff(c_107, plain, (![A_57]: (~v1_xboole_0(k1_relat_1(A_57)) | ~v1_xboole_0(A_57))), inference(splitLeft, [status(thm)], [c_81])).
% 3.36/1.78  tff(c_114, plain, (![A_15]: (~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_20, c_107])).
% 3.36/1.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.78  tff(c_117, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_114, c_4])).
% 3.36/1.78  tff(c_165, plain, (![C_75, B_76, A_77]: (r2_hidden(C_75, B_76) | ~r2_hidden(C_75, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.36/1.78  tff(c_187, plain, (![A_81, B_82]: (r2_hidden('#skF_1'(A_81), B_82) | ~r1_tarski(A_81, B_82))), inference(resolution, [status(thm)], [c_117, c_165])).
% 3.36/1.78  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.36/1.78  tff(c_207, plain, (![A_86, B_87]: (m1_subset_1('#skF_1'(A_86), B_87) | ~r1_tarski(A_86, B_87))), inference(resolution, [status(thm)], [c_187, c_14])).
% 3.36/1.78  tff(c_57, plain, (![A_49]: (v1_xboole_0(A_49) | r2_hidden('#skF_1'(A_49), A_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.78  tff(c_34, plain, (![D_40]: (~r2_hidden(D_40, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_40, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.78  tff(c_68, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_57, c_34])).
% 3.36/1.78  tff(c_120, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_114, c_68])).
% 3.36/1.78  tff(c_221, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_207, c_120])).
% 3.36/1.78  tff(c_272, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_221])).
% 3.36/1.78  tff(c_283, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_272])).
% 3.36/1.78  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_251, c_283])).
% 3.36/1.78  tff(c_288, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_81])).
% 3.36/1.78  tff(c_468, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.36/1.78  tff(c_487, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_468])).
% 3.36/1.78  tff(c_488, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_487, c_36])).
% 3.36/1.78  tff(c_313, plain, (![C_96, A_97, B_98]: (v1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.36/1.78  tff(c_322, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_313])).
% 3.36/1.78  tff(c_354, plain, (![C_109, B_110, A_111]: (v5_relat_1(C_109, B_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.78  tff(c_368, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_354])).
% 3.36/1.78  tff(c_387, plain, (![C_119, B_120, A_121]: (r2_hidden(C_119, B_120) | ~r2_hidden(C_119, A_121) | ~r1_tarski(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.36/1.78  tff(c_409, plain, (![A_125, B_126]: (r2_hidden('#skF_1'(A_125), B_126) | ~r1_tarski(A_125, B_126) | v1_xboole_0(A_125))), inference(resolution, [status(thm)], [c_4, c_387])).
% 3.36/1.78  tff(c_424, plain, (![A_125, B_126]: (m1_subset_1('#skF_1'(A_125), B_126) | ~r1_tarski(A_125, B_126) | v1_xboole_0(A_125))), inference(resolution, [status(thm)], [c_409, c_14])).
% 3.36/1.78  tff(c_593, plain, (![A_154, B_155, C_156]: (k2_relset_1(A_154, B_155, C_156)=k2_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.36/1.78  tff(c_617, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_593])).
% 3.36/1.78  tff(c_298, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 3.36/1.78  tff(c_620, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_298])).
% 3.36/1.78  tff(c_629, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_424, c_620])).
% 3.36/1.78  tff(c_666, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_629])).
% 3.36/1.78  tff(c_669, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_666])).
% 3.36/1.78  tff(c_676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_322, c_368, c_669])).
% 3.36/1.78  tff(c_677, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_629])).
% 3.36/1.78  tff(c_22, plain, (![A_16]: (~v1_xboole_0(k2_relat_1(A_16)) | ~v1_relat_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.36/1.78  tff(c_683, plain, (~v1_relat_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_677, c_22])).
% 3.36/1.78  tff(c_695, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_683])).
% 3.36/1.78  tff(c_49, plain, (![A_44]: (k1_relat_1(A_44)=k1_xboole_0 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_45, c_12])).
% 3.36/1.78  tff(c_706, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_695, c_49])).
% 3.36/1.78  tff(c_713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_488, c_706])).
% 3.36/1.78  tff(c_714, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_68])).
% 3.36/1.78  tff(c_737, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_714, c_12])).
% 3.36/1.78  tff(c_1003, plain, (![A_210, B_211, C_212]: (k2_relset_1(A_210, B_211, C_212)=k2_relat_1(C_212) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.36/1.78  tff(c_1018, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_1003])).
% 3.36/1.78  tff(c_1023, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_737, c_1018])).
% 3.36/1.78  tff(c_1038, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1023, c_22])).
% 3.36/1.78  tff(c_1050, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_786, c_288, c_1038])).
% 3.36/1.78  tff(c_1054, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1050, c_49])).
% 3.36/1.78  tff(c_1061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_896, c_1054])).
% 3.36/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.78  
% 3.36/1.78  Inference rules
% 3.36/1.78  ----------------------
% 3.36/1.78  #Ref     : 0
% 3.36/1.78  #Sup     : 208
% 3.36/1.78  #Fact    : 0
% 3.36/1.78  #Define  : 0
% 3.36/1.78  #Split   : 4
% 3.36/1.78  #Chain   : 0
% 3.36/1.78  #Close   : 0
% 3.36/1.78  
% 3.36/1.78  Ordering : KBO
% 3.36/1.78  
% 3.36/1.78  Simplification rules
% 3.36/1.78  ----------------------
% 3.36/1.78  #Subsume      : 28
% 3.36/1.78  #Demod        : 55
% 3.36/1.78  #Tautology    : 48
% 3.36/1.78  #SimpNegUnit  : 8
% 3.36/1.78  #BackRed      : 16
% 3.36/1.78  
% 3.36/1.78  #Partial instantiations: 0
% 3.36/1.78  #Strategies tried      : 1
% 3.36/1.78  
% 3.36/1.78  Timing (in seconds)
% 3.36/1.78  ----------------------
% 3.67/1.78  Preprocessing        : 0.44
% 3.67/1.78  Parsing              : 0.20
% 3.67/1.78  CNF conversion       : 0.04
% 3.67/1.78  Main loop            : 0.47
% 3.67/1.78  Inferencing          : 0.18
% 3.67/1.78  Reduction            : 0.13
% 3.67/1.78  Demodulation         : 0.08
% 3.67/1.78  BG Simplification    : 0.03
% 3.67/1.78  Subsumption          : 0.09
% 3.67/1.78  Abstraction          : 0.03
% 3.67/1.78  MUC search           : 0.00
% 3.67/1.78  Cooper               : 0.00
% 3.67/1.78  Total                : 0.98
% 3.67/1.78  Index Insertion      : 0.00
% 3.67/1.78  Index Deletion       : 0.00
% 3.67/1.78  Index Matching       : 0.00
% 3.67/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
