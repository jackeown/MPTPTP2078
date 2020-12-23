%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:15 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 309 expanded)
%              Number of leaves         :   35 ( 116 expanded)
%              Depth                    :   13
%              Number of atoms          :  151 ( 633 expanded)
%              Number of equality atoms :   28 (  84 expanded)
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

tff(f_108,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1032,plain,(
    ! [A_207,B_208,C_209] :
      ( k1_relset_1(A_207,B_208,C_209) = k1_relat_1(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1051,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1032])).

tff(c_38,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1052,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1051,c_38])).

tff(c_24,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_94,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_94])).

tff(c_105,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_101])).

tff(c_187,plain,(
    ! [C_82,B_83,A_84] :
      ( v5_relat_1(C_82,B_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_201,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_187])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_381,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_405,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_381])).

tff(c_22,plain,(
    ! [A_18] :
      ( v1_xboole_0(k1_relat_1(A_18))
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    ! [A_48] :
      ( v1_xboole_0(k1_relat_1(A_48))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    ! [A_49] :
      ( k1_relat_1(A_49) = k1_xboole_0
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_48,c_12])).

tff(c_75,plain,(
    ! [A_55] :
      ( k1_relat_1(k1_relat_1(A_55)) = k1_xboole_0
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_84,plain,(
    ! [A_55] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_55))
      | ~ v1_xboole_0(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_22])).

tff(c_107,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(k1_relat_1(A_59))
      | ~ v1_xboole_0(A_59) ) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_114,plain,(
    ! [A_18] : ~ v1_xboole_0(A_18) ),
    inference(resolution,[status(thm)],[c_22,c_107])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_4])).

tff(c_180,plain,(
    ! [C_79,B_80,A_81] :
      ( r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_202,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85),B_86)
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_118,c_180])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_216,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1('#skF_1'(A_89),B_90)
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_202,c_14])).

tff(c_121,plain,(
    ! [A_61] : r2_hidden('#skF_1'(A_61),A_61) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_4])).

tff(c_36,plain,(
    ! [D_42] :
      ( ~ r2_hidden(D_42,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_130,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_121,c_36])).

tff(c_234,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_216,c_130])).

tff(c_409,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_234])).

tff(c_423,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_409])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_201,c_423])).

tff(c_428,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_523,plain,(
    ! [C_143,B_144,A_145] :
      ( v5_relat_1(C_143,B_144)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_537,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_523])).

tff(c_500,plain,(
    ! [C_137,B_138,A_139] :
      ( r2_hidden(C_137,B_138)
      | ~ r2_hidden(C_137,A_139)
      | ~ r1_tarski(A_139,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_539,plain,(
    ! [A_148,B_149] :
      ( r2_hidden('#skF_1'(A_148),B_149)
      | ~ r1_tarski(A_148,B_149)
      | v1_xboole_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_4,c_500])).

tff(c_553,plain,(
    ! [A_148,B_149] :
      ( m1_subset_1('#skF_1'(A_148),B_149)
      | ~ r1_tarski(A_148,B_149)
      | v1_xboole_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_539,c_14])).

tff(c_637,plain,(
    ! [A_161,B_162,C_163] :
      ( k2_relset_1(A_161,B_162,C_163) = k2_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_656,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_637])).

tff(c_59,plain,(
    ! [A_51] :
      ( v1_xboole_0(A_51)
      | r2_hidden('#skF_1'(A_51),A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_59,c_36])).

tff(c_452,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_659,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_452])).

tff(c_668,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_553,c_659])).

tff(c_701,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_668])).

tff(c_704,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_701])).

tff(c_711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_537,c_704])).

tff(c_712,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_668])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(k2_relat_1(A_21))
      | ~ v1_relat_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_718,plain,
    ( ~ v1_relat_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_712,c_26])).

tff(c_730,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_718])).

tff(c_760,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_730,c_12])).

tff(c_765,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_38])).

tff(c_52,plain,(
    ! [A_48] :
      ( k1_relat_1(A_48) = k1_xboole_0
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_48,c_12])).

tff(c_759,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_730,c_52])).

tff(c_815,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_759])).

tff(c_733,plain,(
    ! [A_167,B_168,C_169] :
      ( k1_relset_1(A_167,B_168,C_169) = k1_relat_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_752,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_733])).

tff(c_831,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_752])).

tff(c_832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_765,c_831])).

tff(c_833,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_842,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_833,c_12])).

tff(c_1136,plain,(
    ! [A_224,B_225,C_226] :
      ( k2_relset_1(A_224,B_225,C_226) = k2_relat_1(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1155,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1136])).

tff(c_1161,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_1155])).

tff(c_1179,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1161,c_26])).

tff(c_1193,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_428,c_1179])).

tff(c_1197,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1193,c_52])).

tff(c_1204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1052,c_1197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:13:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.53  
% 3.28/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.53  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.28/1.53  
% 3.28/1.53  %Foreground sorts:
% 3.28/1.53  
% 3.28/1.53  
% 3.28/1.53  %Background operators:
% 3.28/1.53  
% 3.28/1.53  
% 3.28/1.53  %Foreground operators:
% 3.28/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.28/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.28/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.28/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.28/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.28/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.28/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.53  
% 3.42/1.55  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.42/1.55  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.42/1.55  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.42/1.55  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.42/1.55  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.42/1.55  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.42/1.55  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.42/1.55  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.42/1.55  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.42/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.42/1.55  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.42/1.55  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.42/1.55  tff(f_73, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.42/1.55  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.42/1.55  tff(c_1032, plain, (![A_207, B_208, C_209]: (k1_relset_1(A_207, B_208, C_209)=k1_relat_1(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.42/1.55  tff(c_1051, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1032])).
% 3.42/1.55  tff(c_38, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.42/1.55  tff(c_1052, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1051, c_38])).
% 3.42/1.55  tff(c_24, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.42/1.55  tff(c_94, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.42/1.55  tff(c_101, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_94])).
% 3.42/1.55  tff(c_105, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_101])).
% 3.42/1.55  tff(c_187, plain, (![C_82, B_83, A_84]: (v5_relat_1(C_82, B_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.42/1.55  tff(c_201, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_187])).
% 3.42/1.55  tff(c_20, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.42/1.55  tff(c_381, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.42/1.55  tff(c_405, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_381])).
% 3.42/1.55  tff(c_22, plain, (![A_18]: (v1_xboole_0(k1_relat_1(A_18)) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.42/1.55  tff(c_48, plain, (![A_48]: (v1_xboole_0(k1_relat_1(A_48)) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.42/1.55  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.42/1.55  tff(c_53, plain, (![A_49]: (k1_relat_1(A_49)=k1_xboole_0 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_48, c_12])).
% 3.42/1.55  tff(c_75, plain, (![A_55]: (k1_relat_1(k1_relat_1(A_55))=k1_xboole_0 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_22, c_53])).
% 3.42/1.55  tff(c_84, plain, (![A_55]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_55)) | ~v1_xboole_0(A_55))), inference(superposition, [status(thm), theory('equality')], [c_75, c_22])).
% 3.42/1.55  tff(c_107, plain, (![A_59]: (~v1_xboole_0(k1_relat_1(A_59)) | ~v1_xboole_0(A_59))), inference(splitLeft, [status(thm)], [c_84])).
% 3.42/1.55  tff(c_114, plain, (![A_18]: (~v1_xboole_0(A_18))), inference(resolution, [status(thm)], [c_22, c_107])).
% 3.42/1.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.55  tff(c_118, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_114, c_4])).
% 3.42/1.55  tff(c_180, plain, (![C_79, B_80, A_81]: (r2_hidden(C_79, B_80) | ~r2_hidden(C_79, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.42/1.55  tff(c_202, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85), B_86) | ~r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_118, c_180])).
% 3.42/1.55  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.42/1.55  tff(c_216, plain, (![A_89, B_90]: (m1_subset_1('#skF_1'(A_89), B_90) | ~r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_202, c_14])).
% 3.42/1.55  tff(c_121, plain, (![A_61]: (r2_hidden('#skF_1'(A_61), A_61))), inference(negUnitSimplification, [status(thm)], [c_114, c_4])).
% 3.42/1.55  tff(c_36, plain, (![D_42]: (~r2_hidden(D_42, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.42/1.55  tff(c_130, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_121, c_36])).
% 3.42/1.55  tff(c_234, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_216, c_130])).
% 3.42/1.55  tff(c_409, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_405, c_234])).
% 3.42/1.55  tff(c_423, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_409])).
% 3.42/1.55  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_201, c_423])).
% 3.42/1.55  tff(c_428, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_84])).
% 3.42/1.55  tff(c_523, plain, (![C_143, B_144, A_145]: (v5_relat_1(C_143, B_144) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.42/1.55  tff(c_537, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_523])).
% 3.42/1.55  tff(c_500, plain, (![C_137, B_138, A_139]: (r2_hidden(C_137, B_138) | ~r2_hidden(C_137, A_139) | ~r1_tarski(A_139, B_138))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.42/1.55  tff(c_539, plain, (![A_148, B_149]: (r2_hidden('#skF_1'(A_148), B_149) | ~r1_tarski(A_148, B_149) | v1_xboole_0(A_148))), inference(resolution, [status(thm)], [c_4, c_500])).
% 3.42/1.55  tff(c_553, plain, (![A_148, B_149]: (m1_subset_1('#skF_1'(A_148), B_149) | ~r1_tarski(A_148, B_149) | v1_xboole_0(A_148))), inference(resolution, [status(thm)], [c_539, c_14])).
% 3.42/1.55  tff(c_637, plain, (![A_161, B_162, C_163]: (k2_relset_1(A_161, B_162, C_163)=k2_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.42/1.55  tff(c_656, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_637])).
% 3.42/1.55  tff(c_59, plain, (![A_51]: (v1_xboole_0(A_51) | r2_hidden('#skF_1'(A_51), A_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.55  tff(c_67, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_59, c_36])).
% 3.42/1.55  tff(c_452, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_67])).
% 3.42/1.55  tff(c_659, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_656, c_452])).
% 3.42/1.55  tff(c_668, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_553, c_659])).
% 3.42/1.55  tff(c_701, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_668])).
% 3.42/1.55  tff(c_704, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_701])).
% 3.42/1.55  tff(c_711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_537, c_704])).
% 3.42/1.55  tff(c_712, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_668])).
% 3.42/1.55  tff(c_26, plain, (![A_21]: (~v1_xboole_0(k2_relat_1(A_21)) | ~v1_relat_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.42/1.55  tff(c_718, plain, (~v1_relat_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_712, c_26])).
% 3.42/1.55  tff(c_730, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_718])).
% 3.42/1.55  tff(c_760, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_730, c_12])).
% 3.42/1.55  tff(c_765, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_760, c_38])).
% 3.42/1.55  tff(c_52, plain, (![A_48]: (k1_relat_1(A_48)=k1_xboole_0 | ~v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_48, c_12])).
% 3.42/1.55  tff(c_759, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_730, c_52])).
% 3.42/1.55  tff(c_815, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_760, c_759])).
% 3.42/1.55  tff(c_733, plain, (![A_167, B_168, C_169]: (k1_relset_1(A_167, B_168, C_169)=k1_relat_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.42/1.55  tff(c_752, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_733])).
% 3.42/1.55  tff(c_831, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_815, c_752])).
% 3.42/1.55  tff(c_832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_765, c_831])).
% 3.42/1.55  tff(c_833, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_67])).
% 3.42/1.55  tff(c_842, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_833, c_12])).
% 3.42/1.55  tff(c_1136, plain, (![A_224, B_225, C_226]: (k2_relset_1(A_224, B_225, C_226)=k2_relat_1(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.42/1.55  tff(c_1155, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1136])).
% 3.42/1.55  tff(c_1161, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_842, c_1155])).
% 3.42/1.55  tff(c_1179, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1161, c_26])).
% 3.42/1.55  tff(c_1193, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_428, c_1179])).
% 3.42/1.55  tff(c_1197, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1193, c_52])).
% 3.42/1.55  tff(c_1204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1052, c_1197])).
% 3.42/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  Inference rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Ref     : 0
% 3.42/1.55  #Sup     : 232
% 3.42/1.55  #Fact    : 0
% 3.42/1.55  #Define  : 0
% 3.42/1.55  #Split   : 7
% 3.42/1.55  #Chain   : 0
% 3.42/1.55  #Close   : 0
% 3.42/1.55  
% 3.42/1.55  Ordering : KBO
% 3.42/1.55  
% 3.42/1.55  Simplification rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Subsume      : 27
% 3.42/1.55  #Demod        : 91
% 3.42/1.55  #Tautology    : 62
% 3.42/1.55  #SimpNegUnit  : 8
% 3.42/1.55  #BackRed      : 29
% 3.42/1.55  
% 3.42/1.55  #Partial instantiations: 0
% 3.42/1.55  #Strategies tried      : 1
% 3.42/1.55  
% 3.42/1.55  Timing (in seconds)
% 3.42/1.55  ----------------------
% 3.42/1.56  Preprocessing        : 0.33
% 3.42/1.56  Parsing              : 0.18
% 3.42/1.56  CNF conversion       : 0.02
% 3.42/1.56  Main loop            : 0.43
% 3.42/1.56  Inferencing          : 0.17
% 3.42/1.56  Reduction            : 0.13
% 3.42/1.56  Demodulation         : 0.08
% 3.42/1.56  BG Simplification    : 0.02
% 3.42/1.56  Subsumption          : 0.08
% 3.42/1.56  Abstraction          : 0.02
% 3.42/1.56  MUC search           : 0.00
% 3.42/1.56  Cooper               : 0.00
% 3.42/1.56  Total                : 0.80
% 3.42/1.56  Index Insertion      : 0.00
% 3.42/1.56  Index Deletion       : 0.00
% 3.42/1.56  Index Matching       : 0.00
% 3.42/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
