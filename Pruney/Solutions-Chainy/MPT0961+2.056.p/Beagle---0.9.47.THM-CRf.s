%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:49 EST 2020

% Result     : Theorem 10.09s
% Output     : CNFRefutation 10.09s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 472 expanded)
%              Number of leaves         :   33 ( 169 expanded)
%              Depth                    :   13
%              Number of atoms          :  150 (1049 expanded)
%              Number of equality atoms :   48 ( 325 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
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

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_58,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_19133,plain,(
    ! [A_420] :
      ( r1_tarski(A_420,k2_zfmisc_1(k1_relat_1(A_420),k2_relat_1(A_420)))
      | ~ v1_relat_1(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    ! [A_30] :
      ( r1_tarski(A_30,k2_zfmisc_1(k1_relat_1(A_30),k2_relat_1(A_30)))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_206,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_314,plain,(
    ! [A_93,B_94,A_95] :
      ( k1_relset_1(A_93,B_94,A_95) = k1_relat_1(A_95)
      | ~ r1_tarski(A_95,k2_zfmisc_1(A_93,B_94)) ) ),
    inference(resolution,[status(thm)],[c_18,c_206])).

tff(c_333,plain,(
    ! [A_30] :
      ( k1_relset_1(k1_relat_1(A_30),k2_relat_1(A_30),A_30) = k1_relat_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(resolution,[status(thm)],[c_32,c_314])).

tff(c_586,plain,(
    ! [B_127,C_128,A_129] :
      ( k1_xboole_0 = B_127
      | v1_funct_2(C_128,A_129,B_127)
      | k1_relset_1(A_129,B_127,C_128) != A_129
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2292,plain,(
    ! [B_189,A_190,A_191] :
      ( k1_xboole_0 = B_189
      | v1_funct_2(A_190,A_191,B_189)
      | k1_relset_1(A_191,B_189,A_190) != A_191
      | ~ r1_tarski(A_190,k2_zfmisc_1(A_191,B_189)) ) ),
    inference(resolution,[status(thm)],[c_18,c_586])).

tff(c_18466,plain,(
    ! [A_399] :
      ( k2_relat_1(A_399) = k1_xboole_0
      | v1_funct_2(A_399,k1_relat_1(A_399),k2_relat_1(A_399))
      | k1_relset_1(k1_relat_1(A_399),k2_relat_1(A_399),A_399) != k1_relat_1(A_399)
      | ~ v1_relat_1(A_399) ) ),
    inference(resolution,[status(thm)],[c_32,c_2292])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54])).

tff(c_98,plain,(
    ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_18473,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18466,c_98])).

tff(c_18536,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18473])).

tff(c_18541,plain,(
    k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_18536])).

tff(c_18544,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_18541])).

tff(c_18548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18544])).

tff(c_18549,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18536])).

tff(c_18572,plain,
    ( r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),k1_xboole_0))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_18549,c_32])).

tff(c_18589,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12,c_18572])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_666,plain,(
    ! [A_134,B_135] :
      ( r2_hidden(k4_tarski('#skF_2'(A_134,B_135),'#skF_3'(A_134,B_135)),A_134)
      | r2_hidden('#skF_4'(A_134,B_135),B_135)
      | k1_relat_1(A_134) = B_135 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_218,plain,(
    ! [C_78,A_79] :
      ( r2_hidden(k4_tarski(C_78,'#skF_5'(A_79,k1_relat_1(A_79),C_78)),A_79)
      | ~ r2_hidden(C_78,k1_relat_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_229,plain,(
    ! [C_78] :
      ( r2_hidden(k4_tarski(C_78,'#skF_5'(k1_xboole_0,k1_xboole_0,C_78)),k1_xboole_0)
      | ~ r2_hidden(C_78,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_218])).

tff(c_390,plain,(
    ! [C_103] :
      ( r2_hidden(k4_tarski(C_103,'#skF_5'(k1_xboole_0,k1_xboole_0,C_103)),k1_xboole_0)
      | ~ r2_hidden(C_103,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_229])).

tff(c_38,plain,(
    ! [B_32,A_31] :
      ( ~ r1_tarski(B_32,A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_398,plain,(
    ! [C_103] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_103,'#skF_5'(k1_xboole_0,k1_xboole_0,C_103)))
      | ~ r2_hidden(C_103,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_390,c_38])).

tff(c_406,plain,(
    ! [C_103] : ~ r2_hidden(C_103,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_398])).

tff(c_682,plain,(
    ! [B_135] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_135),B_135)
      | k1_relat_1(k1_xboole_0) = B_135 ) ),
    inference(resolution,[status(thm)],[c_666,c_406])).

tff(c_699,plain,(
    ! [B_136] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_136),B_136)
      | k1_xboole_0 = B_136 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_682])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1218,plain,(
    ! [B_153,B_154] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_153),B_154)
      | ~ r1_tarski(B_153,B_154)
      | k1_xboole_0 = B_153 ) ),
    inference(resolution,[status(thm)],[c_699,c_2])).

tff(c_1243,plain,(
    ! [B_153] :
      ( ~ r1_tarski(B_153,k1_xboole_0)
      | k1_xboole_0 = B_153 ) ),
    inference(resolution,[status(thm)],[c_1218,c_406])).

tff(c_18662,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_18589,c_1243])).

tff(c_42,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_36,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_63,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_148,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_151,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_148])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_151])).

tff(c_157,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_261,plain,(
    ! [B_85,C_86] :
      ( k1_relset_1(k1_xboole_0,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_206])).

tff(c_263,plain,(
    ! [B_85] : k1_relset_1(k1_xboole_0,B_85,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_157,c_261])).

tff(c_268,plain,(
    ! [B_85] : k1_relset_1(k1_xboole_0,B_85,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_263])).

tff(c_46,plain,(
    ! [C_38,B_37] :
      ( v1_funct_2(C_38,k1_xboole_0,B_37)
      | k1_relset_1(k1_xboole_0,B_37,C_38) != k1_xboole_0
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_285,plain,(
    ! [C_88,B_89] :
      ( v1_funct_2(C_88,k1_xboole_0,B_89)
      | k1_relset_1(k1_xboole_0,B_89,C_88) != k1_xboole_0
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_287,plain,(
    ! [B_89] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_89)
      | k1_relset_1(k1_xboole_0,B_89,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_157,c_285])).

tff(c_293,plain,(
    ! [B_89] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_287])).

tff(c_18781,plain,(
    ! [B_89] : v1_funct_2('#skF_6','#skF_6',B_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18662,c_18662,c_293])).

tff(c_471,plain,(
    ! [C_118,A_119,B_120] :
      ( r2_hidden(k4_tarski(C_118,'#skF_5'(A_119,k1_relat_1(A_119),C_118)),B_120)
      | ~ r1_tarski(A_119,B_120)
      | ~ r2_hidden(C_118,k1_relat_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_218,c_2])).

tff(c_487,plain,(
    ! [A_119,C_118] :
      ( ~ r1_tarski(A_119,k1_xboole_0)
      | ~ r2_hidden(C_118,k1_relat_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_471,c_406])).

tff(c_723,plain,(
    ! [A_119] :
      ( ~ r1_tarski(A_119,k1_xboole_0)
      | k1_relat_1(A_119) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_699,c_487])).

tff(c_18663,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18589,c_723])).

tff(c_18801,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18662,c_18663])).

tff(c_18551,plain,(
    ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18549,c_98])).

tff(c_18671,plain,(
    ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18662,c_18551])).

tff(c_19048,plain,(
    ~ v1_funct_2('#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18801,c_18671])).

tff(c_19091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18781,c_19048])).

tff(c_19092,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_19102,plain,(
    ~ r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_18,c_19092])).

tff(c_19136,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_19133,c_19102])).

tff(c_19146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_19136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.09/3.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.09/3.91  
% 10.09/3.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.09/3.91  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 10.09/3.91  
% 10.09/3.91  %Foreground sorts:
% 10.09/3.91  
% 10.09/3.91  
% 10.09/3.91  %Background operators:
% 10.09/3.91  
% 10.09/3.91  
% 10.09/3.91  %Foreground operators:
% 10.09/3.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.09/3.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.09/3.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.09/3.91  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.09/3.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.09/3.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.09/3.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.09/3.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.09/3.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.09/3.91  tff('#skF_6', type, '#skF_6': $i).
% 10.09/3.91  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.09/3.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.09/3.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.09/3.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.09/3.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.09/3.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.09/3.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.09/3.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.09/3.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.09/3.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.09/3.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.09/3.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.09/3.91  
% 10.09/3.92  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 10.09/3.92  tff(f_56, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 10.09/3.92  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.09/3.92  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.09/3.92  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.09/3.92  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.09/3.93  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 10.09/3.93  tff(f_52, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 10.09/3.93  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.09/3.93  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 10.09/3.93  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.09/3.93  tff(c_58, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.09/3.93  tff(c_19133, plain, (![A_420]: (r1_tarski(A_420, k2_zfmisc_1(k1_relat_1(A_420), k2_relat_1(A_420))) | ~v1_relat_1(A_420))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.09/3.93  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.09/3.93  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.09/3.93  tff(c_32, plain, (![A_30]: (r1_tarski(A_30, k2_zfmisc_1(k1_relat_1(A_30), k2_relat_1(A_30))) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.09/3.93  tff(c_206, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.09/3.93  tff(c_314, plain, (![A_93, B_94, A_95]: (k1_relset_1(A_93, B_94, A_95)=k1_relat_1(A_95) | ~r1_tarski(A_95, k2_zfmisc_1(A_93, B_94)))), inference(resolution, [status(thm)], [c_18, c_206])).
% 10.09/3.93  tff(c_333, plain, (![A_30]: (k1_relset_1(k1_relat_1(A_30), k2_relat_1(A_30), A_30)=k1_relat_1(A_30) | ~v1_relat_1(A_30))), inference(resolution, [status(thm)], [c_32, c_314])).
% 10.09/3.93  tff(c_586, plain, (![B_127, C_128, A_129]: (k1_xboole_0=B_127 | v1_funct_2(C_128, A_129, B_127) | k1_relset_1(A_129, B_127, C_128)!=A_129 | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_127))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.09/3.93  tff(c_2292, plain, (![B_189, A_190, A_191]: (k1_xboole_0=B_189 | v1_funct_2(A_190, A_191, B_189) | k1_relset_1(A_191, B_189, A_190)!=A_191 | ~r1_tarski(A_190, k2_zfmisc_1(A_191, B_189)))), inference(resolution, [status(thm)], [c_18, c_586])).
% 10.09/3.93  tff(c_18466, plain, (![A_399]: (k2_relat_1(A_399)=k1_xboole_0 | v1_funct_2(A_399, k1_relat_1(A_399), k2_relat_1(A_399)) | k1_relset_1(k1_relat_1(A_399), k2_relat_1(A_399), A_399)!=k1_relat_1(A_399) | ~v1_relat_1(A_399))), inference(resolution, [status(thm)], [c_32, c_2292])).
% 10.09/3.93  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.09/3.93  tff(c_54, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6')))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.09/3.93  tff(c_60, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6')))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54])).
% 10.09/3.93  tff(c_98, plain, (~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_60])).
% 10.09/3.93  tff(c_18473, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18466, c_98])).
% 10.09/3.93  tff(c_18536, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18473])).
% 10.09/3.93  tff(c_18541, plain, (k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6')), inference(splitLeft, [status(thm)], [c_18536])).
% 10.09/3.93  tff(c_18544, plain, (~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_333, c_18541])).
% 10.09/3.93  tff(c_18548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_18544])).
% 10.09/3.93  tff(c_18549, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_18536])).
% 10.09/3.93  tff(c_18572, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), k1_xboole_0)) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_18549, c_32])).
% 10.09/3.93  tff(c_18589, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12, c_18572])).
% 10.09/3.93  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.09/3.93  tff(c_666, plain, (![A_134, B_135]: (r2_hidden(k4_tarski('#skF_2'(A_134, B_135), '#skF_3'(A_134, B_135)), A_134) | r2_hidden('#skF_4'(A_134, B_135), B_135) | k1_relat_1(A_134)=B_135)), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.09/3.93  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.09/3.93  tff(c_218, plain, (![C_78, A_79]: (r2_hidden(k4_tarski(C_78, '#skF_5'(A_79, k1_relat_1(A_79), C_78)), A_79) | ~r2_hidden(C_78, k1_relat_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.09/3.93  tff(c_229, plain, (![C_78]: (r2_hidden(k4_tarski(C_78, '#skF_5'(k1_xboole_0, k1_xboole_0, C_78)), k1_xboole_0) | ~r2_hidden(C_78, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_218])).
% 10.09/3.93  tff(c_390, plain, (![C_103]: (r2_hidden(k4_tarski(C_103, '#skF_5'(k1_xboole_0, k1_xboole_0, C_103)), k1_xboole_0) | ~r2_hidden(C_103, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_229])).
% 10.09/3.93  tff(c_38, plain, (![B_32, A_31]: (~r1_tarski(B_32, A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.09/3.93  tff(c_398, plain, (![C_103]: (~r1_tarski(k1_xboole_0, k4_tarski(C_103, '#skF_5'(k1_xboole_0, k1_xboole_0, C_103))) | ~r2_hidden(C_103, k1_xboole_0))), inference(resolution, [status(thm)], [c_390, c_38])).
% 10.09/3.93  tff(c_406, plain, (![C_103]: (~r2_hidden(C_103, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_398])).
% 10.09/3.93  tff(c_682, plain, (![B_135]: (r2_hidden('#skF_4'(k1_xboole_0, B_135), B_135) | k1_relat_1(k1_xboole_0)=B_135)), inference(resolution, [status(thm)], [c_666, c_406])).
% 10.09/3.93  tff(c_699, plain, (![B_136]: (r2_hidden('#skF_4'(k1_xboole_0, B_136), B_136) | k1_xboole_0=B_136)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_682])).
% 10.09/3.93  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.09/3.93  tff(c_1218, plain, (![B_153, B_154]: (r2_hidden('#skF_4'(k1_xboole_0, B_153), B_154) | ~r1_tarski(B_153, B_154) | k1_xboole_0=B_153)), inference(resolution, [status(thm)], [c_699, c_2])).
% 10.09/3.93  tff(c_1243, plain, (![B_153]: (~r1_tarski(B_153, k1_xboole_0) | k1_xboole_0=B_153)), inference(resolution, [status(thm)], [c_1218, c_406])).
% 10.09/3.93  tff(c_18662, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_18589, c_1243])).
% 10.09/3.93  tff(c_42, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_36, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.09/3.93  tff(c_63, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 10.09/3.93  tff(c_148, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_63])).
% 10.09/3.93  tff(c_151, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_148])).
% 10.09/3.93  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_151])).
% 10.09/3.93  tff(c_157, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_63])).
% 10.09/3.93  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.09/3.93  tff(c_261, plain, (![B_85, C_86]: (k1_relset_1(k1_xboole_0, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_206])).
% 10.09/3.93  tff(c_263, plain, (![B_85]: (k1_relset_1(k1_xboole_0, B_85, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_157, c_261])).
% 10.09/3.93  tff(c_268, plain, (![B_85]: (k1_relset_1(k1_xboole_0, B_85, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_263])).
% 10.09/3.93  tff(c_46, plain, (![C_38, B_37]: (v1_funct_2(C_38, k1_xboole_0, B_37) | k1_relset_1(k1_xboole_0, B_37, C_38)!=k1_xboole_0 | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_37))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.09/3.93  tff(c_285, plain, (![C_88, B_89]: (v1_funct_2(C_88, k1_xboole_0, B_89) | k1_relset_1(k1_xboole_0, B_89, C_88)!=k1_xboole_0 | ~m1_subset_1(C_88, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_46])).
% 10.09/3.93  tff(c_287, plain, (![B_89]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_89) | k1_relset_1(k1_xboole_0, B_89, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_157, c_285])).
% 10.09/3.93  tff(c_293, plain, (![B_89]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_89))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_287])).
% 10.09/3.93  tff(c_18781, plain, (![B_89]: (v1_funct_2('#skF_6', '#skF_6', B_89))), inference(demodulation, [status(thm), theory('equality')], [c_18662, c_18662, c_293])).
% 10.09/3.93  tff(c_471, plain, (![C_118, A_119, B_120]: (r2_hidden(k4_tarski(C_118, '#skF_5'(A_119, k1_relat_1(A_119), C_118)), B_120) | ~r1_tarski(A_119, B_120) | ~r2_hidden(C_118, k1_relat_1(A_119)))), inference(resolution, [status(thm)], [c_218, c_2])).
% 10.09/3.93  tff(c_487, plain, (![A_119, C_118]: (~r1_tarski(A_119, k1_xboole_0) | ~r2_hidden(C_118, k1_relat_1(A_119)))), inference(resolution, [status(thm)], [c_471, c_406])).
% 10.09/3.93  tff(c_723, plain, (![A_119]: (~r1_tarski(A_119, k1_xboole_0) | k1_relat_1(A_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_699, c_487])).
% 10.09/3.93  tff(c_18663, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_18589, c_723])).
% 10.09/3.93  tff(c_18801, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_18662, c_18663])).
% 10.09/3.93  tff(c_18551, plain, (~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18549, c_98])).
% 10.09/3.93  tff(c_18671, plain, (~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18662, c_18551])).
% 10.09/3.93  tff(c_19048, plain, (~v1_funct_2('#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18801, c_18671])).
% 10.09/3.93  tff(c_19091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18781, c_19048])).
% 10.09/3.93  tff(c_19092, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))))), inference(splitRight, [status(thm)], [c_60])).
% 10.09/3.93  tff(c_19102, plain, (~r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_18, c_19092])).
% 10.09/3.93  tff(c_19136, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_19133, c_19102])).
% 10.09/3.93  tff(c_19146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_19136])).
% 10.09/3.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.09/3.93  
% 10.09/3.93  Inference rules
% 10.09/3.93  ----------------------
% 10.09/3.93  #Ref     : 0
% 10.09/3.93  #Sup     : 5311
% 10.09/3.93  #Fact    : 0
% 10.09/3.93  #Define  : 0
% 10.09/3.93  #Split   : 3
% 10.09/3.93  #Chain   : 0
% 10.09/3.93  #Close   : 0
% 10.09/3.93  
% 10.09/3.93  Ordering : KBO
% 10.09/3.93  
% 10.09/3.93  Simplification rules
% 10.09/3.93  ----------------------
% 10.09/3.93  #Subsume      : 3072
% 10.09/3.93  #Demod        : 3622
% 10.09/3.93  #Tautology    : 701
% 10.09/3.93  #SimpNegUnit  : 73
% 10.09/3.93  #BackRed      : 128
% 10.09/3.93  
% 10.09/3.93  #Partial instantiations: 0
% 10.09/3.93  #Strategies tried      : 1
% 10.09/3.93  
% 10.09/3.93  Timing (in seconds)
% 10.09/3.93  ----------------------
% 10.09/3.93  Preprocessing        : 0.30
% 10.09/3.93  Parsing              : 0.15
% 10.09/3.93  CNF conversion       : 0.02
% 10.09/3.93  Main loop            : 2.79
% 10.09/3.93  Inferencing          : 0.53
% 10.09/3.93  Reduction            : 0.61
% 10.09/3.93  Demodulation         : 0.45
% 10.09/3.93  BG Simplification    : 0.06
% 10.09/3.93  Subsumption          : 1.42
% 10.09/3.93  Abstraction          : 0.11
% 10.09/3.93  MUC search           : 0.00
% 10.09/3.93  Cooper               : 0.00
% 10.09/3.93  Total                : 3.13
% 10.09/3.93  Index Insertion      : 0.00
% 10.09/3.93  Index Deletion       : 0.00
% 10.09/3.93  Index Matching       : 0.00
% 10.09/3.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
