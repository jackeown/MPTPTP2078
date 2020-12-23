%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:49 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 247 expanded)
%              Number of leaves         :   25 (  95 expanded)
%              Depth                    :    9
%              Number of atoms          :  159 ( 586 expanded)
%              Number of equality atoms :   43 ( 162 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_76,axiom,(
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

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_256,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_1'(A_88,B_89),A_88)
      | r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_261,plain,(
    ! [A_88] : r1_tarski(A_88,A_88) ),
    inference(resolution,[status(thm)],[c_256,c_4])).

tff(c_300,plain,(
    ! [C_112,A_113,B_114] :
      ( m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ r1_tarski(k2_relat_1(C_112),B_114)
      | ~ r1_tarski(k1_relat_1(C_112),A_113)
      | ~ v1_relat_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_85,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),A_26)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_26] : r1_tarski(A_26,A_26) ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_156,plain,(
    ! [C_59,A_60,B_61] :
      ( m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ r1_tarski(k2_relat_1(C_59),B_61)
      | ~ r1_tarski(k1_relat_1(C_59),A_60)
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_174,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ r1_tarski(k2_relat_1(C_69),B_68)
      | ~ r1_tarski(k1_relat_1(C_69),A_67)
      | ~ v1_relat_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_156,c_20])).

tff(c_179,plain,(
    ! [A_70,C_71] :
      ( k1_relset_1(A_70,k2_relat_1(C_71),C_71) = k1_relat_1(C_71)
      | ~ r1_tarski(k1_relat_1(C_71),A_70)
      | ~ v1_relat_1(C_71) ) ),
    inference(resolution,[status(thm)],[c_90,c_174])).

tff(c_183,plain,(
    ! [C_71] :
      ( k1_relset_1(k1_relat_1(C_71),k2_relat_1(C_71),C_71) = k1_relat_1(C_71)
      | ~ v1_relat_1(C_71) ) ),
    inference(resolution,[status(thm)],[c_90,c_179])).

tff(c_71,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) = k1_xboole_0
      | k2_relat_1(A_24) != k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_71])).

tff(c_76,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_22,plain,(
    ! [C_15,A_13,B_14] :
      ( m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ r1_tarski(k2_relat_1(C_15),B_14)
      | ~ r1_tarski(k1_relat_1(C_15),A_13)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_205,plain,(
    ! [B_76,C_77,A_78] :
      ( k1_xboole_0 = B_76
      | v1_funct_2(C_77,A_78,B_76)
      | k1_relset_1(A_78,B_76,C_77) != A_78
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_218,plain,(
    ! [B_82,C_83,A_84] :
      ( k1_xboole_0 = B_82
      | v1_funct_2(C_83,A_84,B_82)
      | k1_relset_1(A_84,B_82,C_83) != A_84
      | ~ r1_tarski(k2_relat_1(C_83),B_82)
      | ~ r1_tarski(k1_relat_1(C_83),A_84)
      | ~ v1_relat_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_22,c_205])).

tff(c_223,plain,(
    ! [C_85,A_86] :
      ( k2_relat_1(C_85) = k1_xboole_0
      | v1_funct_2(C_85,A_86,k2_relat_1(C_85))
      | k1_relset_1(A_86,k2_relat_1(C_85),C_85) != A_86
      | ~ r1_tarski(k1_relat_1(C_85),A_86)
      | ~ v1_relat_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_90,c_218])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_77,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_231,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_223,c_77])).

tff(c_238,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_90,c_231])).

tff(c_239,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_238])).

tff(c_242,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_239])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_242])).

tff(c_247,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_306,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_300,c_247])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_261,c_261,c_306])).

tff(c_318,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_319,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_388,plain,(
    ! [C_144,A_145,B_146] :
      ( m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ r1_tarski(k2_relat_1(C_144),B_146)
      | ~ r1_tarski(k1_relat_1(C_144),A_145)
      | ~ v1_relat_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_419,plain,(
    ! [C_152,B_153] :
      ( m1_subset_1(C_152,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_152),B_153)
      | ~ r1_tarski(k1_relat_1(C_152),k1_xboole_0)
      | ~ v1_relat_1(C_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_388])).

tff(c_425,plain,(
    ! [B_153] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,B_153)
      | ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_419])).

tff(c_428,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8,c_318,c_8,c_425])).

tff(c_370,plain,(
    ! [A_129,B_130,C_131] :
      ( k1_relset_1(A_129,B_130,C_131) = k1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_376,plain,(
    ! [B_8,C_131] :
      ( k1_relset_1(k1_xboole_0,B_8,C_131) = k1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_370])).

tff(c_432,plain,(
    ! [B_8] : k1_relset_1(k1_xboole_0,B_8,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_428,c_376])).

tff(c_437,plain,(
    ! [B_8] : k1_relset_1(k1_xboole_0,B_8,'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_432])).

tff(c_28,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_435,plain,(
    ! [B_17] :
      ( v1_funct_2('#skF_2',k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_428,c_43])).

tff(c_475,plain,(
    ! [B_17] : v1_funct_2('#skF_2',k1_xboole_0,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_435])).

tff(c_358,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2('#skF_2',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_318,c_14,c_318,c_42])).

tff(c_359,plain,(
    ~ v1_funct_2('#skF_2',k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_359])).

tff(c_479,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_328,plain,(
    ! [A_115,B_116] :
      ( r2_hidden('#skF_1'(A_115,B_116),A_115)
      | r1_tarski(A_115,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_333,plain,(
    ! [A_115] : r1_tarski(A_115,A_115) ),
    inference(resolution,[status(thm)],[c_328,c_4])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_524,plain,(
    ! [C_182,A_183,B_184] :
      ( m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ r1_tarski(k2_relat_1(C_182),B_184)
      | ~ r1_tarski(k1_relat_1(C_182),A_183)
      | ~ v1_relat_1(C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_546,plain,(
    ! [C_187,A_188] :
      ( m1_subset_1(C_187,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_187),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_187),A_188)
      | ~ v1_relat_1(C_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_524])).

tff(c_548,plain,(
    ! [A_188] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_188)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_546])).

tff(c_550,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8,c_318,c_333,c_548])).

tff(c_552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_479,c_550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:59:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.39  
% 2.45/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.40  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.76/1.40  
% 2.76/1.40  %Foreground sorts:
% 2.76/1.40  
% 2.76/1.40  
% 2.76/1.40  %Background operators:
% 2.76/1.40  
% 2.76/1.40  
% 2.76/1.40  %Foreground operators:
% 2.76/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.76/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.76/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.40  
% 2.76/1.41  tff(f_87, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.76/1.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.76/1.41  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.76/1.41  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.76/1.41  tff(f_46, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.76/1.41  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.76/1.41  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.76/1.41  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.76/1.41  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.76/1.41  tff(c_256, plain, (![A_88, B_89]: (r2_hidden('#skF_1'(A_88, B_89), A_88) | r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.41  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.41  tff(c_261, plain, (![A_88]: (r1_tarski(A_88, A_88))), inference(resolution, [status(thm)], [c_256, c_4])).
% 2.76/1.41  tff(c_300, plain, (![C_112, A_113, B_114]: (m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~r1_tarski(k2_relat_1(C_112), B_114) | ~r1_tarski(k1_relat_1(C_112), A_113) | ~v1_relat_1(C_112))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.41  tff(c_85, plain, (![A_26, B_27]: (r2_hidden('#skF_1'(A_26, B_27), A_26) | r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.41  tff(c_90, plain, (![A_26]: (r1_tarski(A_26, A_26))), inference(resolution, [status(thm)], [c_85, c_4])).
% 2.76/1.41  tff(c_156, plain, (![C_59, A_60, B_61]: (m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~r1_tarski(k2_relat_1(C_59), B_61) | ~r1_tarski(k1_relat_1(C_59), A_60) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.41  tff(c_20, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.76/1.41  tff(c_174, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~r1_tarski(k2_relat_1(C_69), B_68) | ~r1_tarski(k1_relat_1(C_69), A_67) | ~v1_relat_1(C_69))), inference(resolution, [status(thm)], [c_156, c_20])).
% 2.76/1.41  tff(c_179, plain, (![A_70, C_71]: (k1_relset_1(A_70, k2_relat_1(C_71), C_71)=k1_relat_1(C_71) | ~r1_tarski(k1_relat_1(C_71), A_70) | ~v1_relat_1(C_71))), inference(resolution, [status(thm)], [c_90, c_174])).
% 2.76/1.41  tff(c_183, plain, (![C_71]: (k1_relset_1(k1_relat_1(C_71), k2_relat_1(C_71), C_71)=k1_relat_1(C_71) | ~v1_relat_1(C_71))), inference(resolution, [status(thm)], [c_90, c_179])).
% 2.76/1.41  tff(c_71, plain, (![A_24]: (k1_relat_1(A_24)=k1_xboole_0 | k2_relat_1(A_24)!=k1_xboole_0 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.41  tff(c_75, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k2_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_71])).
% 2.76/1.41  tff(c_76, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_75])).
% 2.76/1.41  tff(c_22, plain, (![C_15, A_13, B_14]: (m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~r1_tarski(k2_relat_1(C_15), B_14) | ~r1_tarski(k1_relat_1(C_15), A_13) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.41  tff(c_205, plain, (![B_76, C_77, A_78]: (k1_xboole_0=B_76 | v1_funct_2(C_77, A_78, B_76) | k1_relset_1(A_78, B_76, C_77)!=A_78 | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_76))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.41  tff(c_218, plain, (![B_82, C_83, A_84]: (k1_xboole_0=B_82 | v1_funct_2(C_83, A_84, B_82) | k1_relset_1(A_84, B_82, C_83)!=A_84 | ~r1_tarski(k2_relat_1(C_83), B_82) | ~r1_tarski(k1_relat_1(C_83), A_84) | ~v1_relat_1(C_83))), inference(resolution, [status(thm)], [c_22, c_205])).
% 2.76/1.41  tff(c_223, plain, (![C_85, A_86]: (k2_relat_1(C_85)=k1_xboole_0 | v1_funct_2(C_85, A_86, k2_relat_1(C_85)) | k1_relset_1(A_86, k2_relat_1(C_85), C_85)!=A_86 | ~r1_tarski(k1_relat_1(C_85), A_86) | ~v1_relat_1(C_85))), inference(resolution, [status(thm)], [c_90, c_218])).
% 2.76/1.41  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.76/1.41  tff(c_36, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.76/1.41  tff(c_42, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 2.76/1.41  tff(c_77, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.76/1.41  tff(c_231, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_223, c_77])).
% 2.76/1.41  tff(c_238, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_90, c_231])).
% 2.76/1.41  tff(c_239, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_76, c_238])).
% 2.76/1.41  tff(c_242, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_183, c_239])).
% 2.76/1.41  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_242])).
% 2.76/1.41  tff(c_247, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_42])).
% 2.76/1.41  tff(c_306, plain, (~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_300, c_247])).
% 2.76/1.41  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_261, c_261, c_306])).
% 2.76/1.41  tff(c_318, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_75])).
% 2.76/1.41  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.41  tff(c_319, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_75])).
% 2.76/1.41  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.41  tff(c_388, plain, (![C_144, A_145, B_146]: (m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~r1_tarski(k2_relat_1(C_144), B_146) | ~r1_tarski(k1_relat_1(C_144), A_145) | ~v1_relat_1(C_144))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.41  tff(c_419, plain, (![C_152, B_153]: (m1_subset_1(C_152, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_152), B_153) | ~r1_tarski(k1_relat_1(C_152), k1_xboole_0) | ~v1_relat_1(C_152))), inference(superposition, [status(thm), theory('equality')], [c_14, c_388])).
% 2.76/1.41  tff(c_425, plain, (![B_153]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, B_153) | ~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_419])).
% 2.76/1.41  tff(c_428, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8, c_318, c_8, c_425])).
% 2.76/1.41  tff(c_370, plain, (![A_129, B_130, C_131]: (k1_relset_1(A_129, B_130, C_131)=k1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.76/1.41  tff(c_376, plain, (![B_8, C_131]: (k1_relset_1(k1_xboole_0, B_8, C_131)=k1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_370])).
% 2.76/1.41  tff(c_432, plain, (![B_8]: (k1_relset_1(k1_xboole_0, B_8, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_428, c_376])).
% 2.76/1.41  tff(c_437, plain, (![B_8]: (k1_relset_1(k1_xboole_0, B_8, '#skF_2')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_318, c_432])).
% 2.76/1.41  tff(c_28, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.41  tff(c_43, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 2.76/1.41  tff(c_435, plain, (![B_17]: (v1_funct_2('#skF_2', k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_428, c_43])).
% 2.76/1.41  tff(c_475, plain, (![B_17]: (v1_funct_2('#skF_2', k1_xboole_0, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_435])).
% 2.76/1.41  tff(c_358, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2('#skF_2', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_319, c_318, c_14, c_318, c_42])).
% 2.76/1.41  tff(c_359, plain, (~v1_funct_2('#skF_2', k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_358])).
% 2.76/1.41  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_475, c_359])).
% 2.76/1.41  tff(c_479, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_358])).
% 2.76/1.41  tff(c_328, plain, (![A_115, B_116]: (r2_hidden('#skF_1'(A_115, B_116), A_115) | r1_tarski(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.41  tff(c_333, plain, (![A_115]: (r1_tarski(A_115, A_115))), inference(resolution, [status(thm)], [c_328, c_4])).
% 2.76/1.41  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.41  tff(c_524, plain, (![C_182, A_183, B_184]: (m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~r1_tarski(k2_relat_1(C_182), B_184) | ~r1_tarski(k1_relat_1(C_182), A_183) | ~v1_relat_1(C_182))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.41  tff(c_546, plain, (![C_187, A_188]: (m1_subset_1(C_187, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_187), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_187), A_188) | ~v1_relat_1(C_187))), inference(superposition, [status(thm), theory('equality')], [c_12, c_524])).
% 2.76/1.41  tff(c_548, plain, (![A_188]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_188) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_546])).
% 2.76/1.41  tff(c_550, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8, c_318, c_333, c_548])).
% 2.76/1.41  tff(c_552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_479, c_550])).
% 2.76/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.41  
% 2.76/1.41  Inference rules
% 2.76/1.41  ----------------------
% 2.76/1.41  #Ref     : 0
% 2.76/1.41  #Sup     : 106
% 2.76/1.41  #Fact    : 0
% 2.76/1.41  #Define  : 0
% 2.76/1.41  #Split   : 6
% 2.76/1.41  #Chain   : 0
% 2.76/1.41  #Close   : 0
% 2.76/1.41  
% 2.76/1.41  Ordering : KBO
% 2.76/1.41  
% 2.76/1.41  Simplification rules
% 2.76/1.41  ----------------------
% 2.76/1.41  #Subsume      : 15
% 2.76/1.41  #Demod        : 36
% 2.76/1.41  #Tautology    : 40
% 2.76/1.41  #SimpNegUnit  : 4
% 2.76/1.41  #BackRed      : 1
% 2.76/1.41  
% 2.76/1.41  #Partial instantiations: 0
% 2.76/1.41  #Strategies tried      : 1
% 2.76/1.41  
% 2.76/1.41  Timing (in seconds)
% 2.76/1.41  ----------------------
% 2.76/1.42  Preprocessing        : 0.33
% 2.76/1.42  Parsing              : 0.17
% 2.76/1.42  CNF conversion       : 0.02
% 2.76/1.42  Main loop            : 0.30
% 2.76/1.42  Inferencing          : 0.12
% 2.76/1.42  Reduction            : 0.08
% 2.76/1.42  Demodulation         : 0.06
% 2.76/1.42  BG Simplification    : 0.02
% 2.76/1.42  Subsumption          : 0.06
% 2.76/1.42  Abstraction          : 0.02
% 2.76/1.42  MUC search           : 0.00
% 2.76/1.42  Cooper               : 0.00
% 2.76/1.42  Total                : 0.67
% 2.76/1.42  Index Insertion      : 0.00
% 2.76/1.42  Index Deletion       : 0.00
% 2.76/1.42  Index Matching       : 0.00
% 2.76/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
