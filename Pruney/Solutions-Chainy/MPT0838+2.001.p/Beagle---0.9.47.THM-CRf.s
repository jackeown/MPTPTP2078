%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:09 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 536 expanded)
%              Number of leaves         :   35 ( 188 expanded)
%              Depth                    :   14
%              Number of atoms          :  208 (1166 expanded)
%              Number of equality atoms :   26 ( 139 expanded)
%              Maximal formula depth    :   13 (   4 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
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

tff(f_81,axiom,(
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

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1127,plain,(
    ! [A_222,B_223,C_224] :
      ( k1_relset_1(A_222,B_223,C_224) = k1_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1146,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1127])).

tff(c_38,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1147,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_38])).

tff(c_101,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_149,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_158,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_149])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_343,plain,(
    ! [A_118,B_119,C_120] :
      ( k2_relset_1(A_118,B_119,C_120) = k2_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_367,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_343])).

tff(c_20,plain,(
    ! [A_15] :
      ( v1_xboole_0(k1_relat_1(A_15))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_47,plain,(
    ! [A_51] :
      ( v1_xboole_0(k1_relat_1(A_51))
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ! [A_52] :
      ( k1_relat_1(A_52) = k1_xboole_0
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_47,c_12])).

tff(c_74,plain,(
    ! [A_58] :
      ( k1_relat_1(k1_relat_1(A_58)) = k1_xboole_0
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_20,c_52])).

tff(c_83,plain,(
    ! [A_58] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_20])).

tff(c_93,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(k1_relat_1(A_59))
      | ~ v1_xboole_0(A_59) ) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_100,plain,(
    ! [A_15] : ~ v1_xboole_0(A_15) ),
    inference(resolution,[status(thm)],[c_20,c_93])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_4])).

tff(c_196,plain,(
    ! [C_88,B_89,A_90] :
      ( r2_hidden(C_88,B_89)
      | ~ r2_hidden(C_88,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_204,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92),B_93)
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_112,c_196])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_217,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1('#skF_1'(A_94),B_95)
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_204,c_14])).

tff(c_115,plain,(
    ! [A_64] : r2_hidden('#skF_1'(A_64),A_64) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_4])).

tff(c_36,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_47,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_123,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_115,c_36])).

tff(c_235,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_217,c_123])).

tff(c_395,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_235])).

tff(c_405,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_395])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_158,c_405])).

tff(c_410,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_927,plain,(
    ! [A_185,B_186] :
      ( r2_hidden('#skF_2'(A_185,B_186),A_185)
      | r1_tarski(A_185,B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_945,plain,(
    ! [A_185,B_186] :
      ( ~ v1_xboole_0(A_185)
      | r1_tarski(A_185,B_186) ) ),
    inference(resolution,[status(thm)],[c_927,c_2])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1005,plain,(
    ! [C_206,B_207,A_208] :
      ( r2_hidden(C_206,B_207)
      | ~ r2_hidden(C_206,A_208)
      | ~ r1_tarski(A_208,B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1152,plain,(
    ! [A_225,B_226,B_227] :
      ( r2_hidden('#skF_2'(A_225,B_226),B_227)
      | ~ r1_tarski(A_225,B_227)
      | r1_tarski(A_225,B_226) ) ),
    inference(resolution,[status(thm)],[c_10,c_1005])).

tff(c_1190,plain,(
    ! [A_233,B_234,B_235] :
      ( m1_subset_1('#skF_2'(A_233,B_234),B_235)
      | ~ r1_tarski(A_233,B_235)
      | r1_tarski(A_233,B_234) ) ),
    inference(resolution,[status(thm)],[c_1152,c_14])).

tff(c_722,plain,(
    ! [A_168,B_169,C_170] :
      ( k1_relset_1(A_168,B_169,C_170) = k1_relat_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_741,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_722])).

tff(c_755,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_38])).

tff(c_436,plain,(
    ! [C_126,A_127,B_128] :
      ( v1_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_445,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_436])).

tff(c_498,plain,(
    ! [C_143,B_144,A_145] :
      ( v5_relat_1(C_143,B_144)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_512,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_498])).

tff(c_491,plain,(
    ! [C_140,B_141,A_142] :
      ( r2_hidden(C_140,B_141)
      | ~ r2_hidden(C_140,A_142)
      | ~ r1_tarski(A_142,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_531,plain,(
    ! [A_153,B_154] :
      ( r2_hidden('#skF_1'(A_153),B_154)
      | ~ r1_tarski(A_153,B_154)
      | v1_xboole_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_4,c_491])).

tff(c_546,plain,(
    ! [A_153,B_154] :
      ( m1_subset_1('#skF_1'(A_153),B_154)
      | ~ r1_tarski(A_153,B_154)
      | v1_xboole_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_531,c_14])).

tff(c_601,plain,(
    ! [A_162,B_163,C_164] :
      ( k2_relset_1(A_162,B_163,C_164) = k2_relat_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_620,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_601])).

tff(c_59,plain,(
    ! [A_56] :
      ( v1_xboole_0(A_56)
      | r2_hidden('#skF_1'(A_56),A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_59,c_36])).

tff(c_420,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_622,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_420])).

tff(c_631,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_546,c_622])).

tff(c_665,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_631])).

tff(c_668,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_665])).

tff(c_675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_512,c_668])).

tff(c_676,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_631])).

tff(c_446,plain,(
    ! [A_129,B_130] :
      ( r2_hidden('#skF_2'(A_129,B_130),A_129)
      | r1_tarski(A_129,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_464,plain,(
    ! [A_129,B_130] :
      ( ~ v1_xboole_0(A_129)
      | r1_tarski(A_129,B_130) ) ),
    inference(resolution,[status(thm)],[c_446,c_2])).

tff(c_513,plain,(
    ! [B_146,A_147] :
      ( v5_relat_1(B_146,A_147)
      | ~ r1_tarski(k2_relat_1(B_146),A_147)
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_522,plain,(
    ! [B_146,B_130] :
      ( v5_relat_1(B_146,B_130)
      | ~ v1_relat_1(B_146)
      | ~ v1_xboole_0(k2_relat_1(B_146)) ) ),
    inference(resolution,[status(thm)],[c_464,c_513])).

tff(c_679,plain,(
    ! [B_130] :
      ( v5_relat_1('#skF_5',B_130)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_676,c_522])).

tff(c_688,plain,(
    ! [B_130] : v5_relat_1('#skF_5',B_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_679])).

tff(c_690,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_676,c_12])).

tff(c_704,plain,(
    ! [A_13] :
      ( r1_tarski(k1_xboole_0,A_13)
      | ~ v5_relat_1('#skF_5',A_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_18])).

tff(c_716,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_688,c_704])).

tff(c_796,plain,(
    ! [D_174,C_175,B_176,A_177] :
      ( m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(C_175,B_176)))
      | ~ r1_tarski(k2_relat_1(D_174),B_176)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(C_175,A_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_807,plain,(
    ! [B_176] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_176)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_176) ) ),
    inference(resolution,[status(thm)],[c_40,c_796])).

tff(c_819,plain,(
    ! [B_178] : m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_178))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_690,c_807])).

tff(c_28,plain,(
    ! [C_25,B_23,A_22] :
      ( v1_xboole_0(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(B_23,A_22)))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_846,plain,(
    ! [B_178] :
      ( v1_xboole_0('#skF_5')
      | ~ v1_xboole_0(B_178) ) ),
    inference(resolution,[status(thm)],[c_819,c_28])).

tff(c_853,plain,(
    ! [B_178] : ~ v1_xboole_0(B_178) ),
    inference(splitLeft,[status(thm)],[c_846])).

tff(c_864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_853,c_410])).

tff(c_865,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_846])).

tff(c_51,plain,(
    ! [A_51] :
      ( k1_relat_1(A_51) = k1_xboole_0
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_47,c_12])).

tff(c_868,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_865,c_51])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_755,c_868])).

tff(c_876,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_899,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_876,c_12])).

tff(c_901,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,k1_xboole_0)
      | ~ m1_subset_1(D_47,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_36])).

tff(c_942,plain,(
    ! [B_186] :
      ( ~ m1_subset_1('#skF_2'(k1_xboole_0,B_186),'#skF_4')
      | r1_tarski(k1_xboole_0,B_186) ) ),
    inference(resolution,[status(thm)],[c_927,c_901])).

tff(c_1224,plain,(
    ! [B_234] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_4')
      | r1_tarski(k1_xboole_0,B_234) ) ),
    inference(resolution,[status(thm)],[c_1190,c_942])).

tff(c_1226,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1224])).

tff(c_1229,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_945,c_1226])).

tff(c_1233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_1229])).

tff(c_1234,plain,(
    ! [B_234] : r1_tarski(k1_xboole_0,B_234) ),
    inference(splitRight,[status(thm)],[c_1224])).

tff(c_1254,plain,(
    ! [A_237,B_238,C_239] :
      ( k2_relset_1(A_237,B_238,C_239) = k2_relat_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1273,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1254])).

tff(c_1279,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_1273])).

tff(c_1366,plain,(
    ! [D_251,C_252,B_253,A_254] :
      ( m1_subset_1(D_251,k1_zfmisc_1(k2_zfmisc_1(C_252,B_253)))
      | ~ r1_tarski(k2_relat_1(D_251),B_253)
      | ~ m1_subset_1(D_251,k1_zfmisc_1(k2_zfmisc_1(C_252,A_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1380,plain,(
    ! [B_253] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_253)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_253) ) ),
    inference(resolution,[status(thm)],[c_40,c_1366])).

tff(c_1389,plain,(
    ! [B_255] : m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_255))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_1279,c_1380])).

tff(c_1416,plain,(
    ! [B_255] :
      ( v1_xboole_0('#skF_5')
      | ~ v1_xboole_0(B_255) ) ),
    inference(resolution,[status(thm)],[c_1389,c_28])).

tff(c_1423,plain,(
    ! [B_255] : ~ v1_xboole_0(B_255) ),
    inference(splitLeft,[status(thm)],[c_1416])).

tff(c_1437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1423,c_410])).

tff(c_1438,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1416])).

tff(c_1449,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1438,c_51])).

tff(c_1456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1147,c_1449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:30:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.54  
% 3.36/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.54  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.36/1.54  
% 3.36/1.54  %Foreground sorts:
% 3.36/1.54  
% 3.36/1.54  
% 3.36/1.54  %Background operators:
% 3.36/1.54  
% 3.36/1.54  
% 3.36/1.54  %Foreground operators:
% 3.36/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.36/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.36/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.36/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.36/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.36/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.36/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.54  
% 3.45/1.56  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.45/1.56  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.45/1.56  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.45/1.56  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.45/1.56  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.45/1.56  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.45/1.56  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.45/1.56  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.45/1.56  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.45/1.56  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.45/1.56  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.45/1.56  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 3.45/1.56  tff(f_73, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.45/1.56  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.45/1.56  tff(c_1127, plain, (![A_222, B_223, C_224]: (k1_relset_1(A_222, B_223, C_224)=k1_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.45/1.56  tff(c_1146, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1127])).
% 3.45/1.56  tff(c_38, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.45/1.56  tff(c_1147, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1146, c_38])).
% 3.45/1.56  tff(c_101, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.45/1.56  tff(c_110, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_101])).
% 3.45/1.56  tff(c_149, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.56  tff(c_158, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_149])).
% 3.45/1.56  tff(c_18, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.45/1.56  tff(c_343, plain, (![A_118, B_119, C_120]: (k2_relset_1(A_118, B_119, C_120)=k2_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.56  tff(c_367, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_343])).
% 3.45/1.56  tff(c_20, plain, (![A_15]: (v1_xboole_0(k1_relat_1(A_15)) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.45/1.56  tff(c_47, plain, (![A_51]: (v1_xboole_0(k1_relat_1(A_51)) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.45/1.56  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.45/1.56  tff(c_52, plain, (![A_52]: (k1_relat_1(A_52)=k1_xboole_0 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_47, c_12])).
% 3.45/1.56  tff(c_74, plain, (![A_58]: (k1_relat_1(k1_relat_1(A_58))=k1_xboole_0 | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_20, c_52])).
% 3.45/1.56  tff(c_83, plain, (![A_58]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_58)) | ~v1_xboole_0(A_58))), inference(superposition, [status(thm), theory('equality')], [c_74, c_20])).
% 3.45/1.56  tff(c_93, plain, (![A_59]: (~v1_xboole_0(k1_relat_1(A_59)) | ~v1_xboole_0(A_59))), inference(splitLeft, [status(thm)], [c_83])).
% 3.45/1.56  tff(c_100, plain, (![A_15]: (~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_20, c_93])).
% 3.45/1.56  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.56  tff(c_112, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_100, c_4])).
% 3.45/1.56  tff(c_196, plain, (![C_88, B_89, A_90]: (r2_hidden(C_88, B_89) | ~r2_hidden(C_88, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.45/1.56  tff(c_204, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92), B_93) | ~r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_112, c_196])).
% 3.45/1.56  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.45/1.56  tff(c_217, plain, (![A_94, B_95]: (m1_subset_1('#skF_1'(A_94), B_95) | ~r1_tarski(A_94, B_95))), inference(resolution, [status(thm)], [c_204, c_14])).
% 3.45/1.56  tff(c_115, plain, (![A_64]: (r2_hidden('#skF_1'(A_64), A_64))), inference(negUnitSimplification, [status(thm)], [c_100, c_4])).
% 3.45/1.56  tff(c_36, plain, (![D_47]: (~r2_hidden(D_47, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_47, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.45/1.56  tff(c_123, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_115, c_36])).
% 3.45/1.56  tff(c_235, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_217, c_123])).
% 3.45/1.56  tff(c_395, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_367, c_235])).
% 3.45/1.56  tff(c_405, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_395])).
% 3.45/1.56  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_158, c_405])).
% 3.45/1.56  tff(c_410, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_83])).
% 3.45/1.56  tff(c_927, plain, (![A_185, B_186]: (r2_hidden('#skF_2'(A_185, B_186), A_185) | r1_tarski(A_185, B_186))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.45/1.56  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.56  tff(c_945, plain, (![A_185, B_186]: (~v1_xboole_0(A_185) | r1_tarski(A_185, B_186))), inference(resolution, [status(thm)], [c_927, c_2])).
% 3.45/1.56  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.45/1.56  tff(c_1005, plain, (![C_206, B_207, A_208]: (r2_hidden(C_206, B_207) | ~r2_hidden(C_206, A_208) | ~r1_tarski(A_208, B_207))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.45/1.56  tff(c_1152, plain, (![A_225, B_226, B_227]: (r2_hidden('#skF_2'(A_225, B_226), B_227) | ~r1_tarski(A_225, B_227) | r1_tarski(A_225, B_226))), inference(resolution, [status(thm)], [c_10, c_1005])).
% 3.45/1.56  tff(c_1190, plain, (![A_233, B_234, B_235]: (m1_subset_1('#skF_2'(A_233, B_234), B_235) | ~r1_tarski(A_233, B_235) | r1_tarski(A_233, B_234))), inference(resolution, [status(thm)], [c_1152, c_14])).
% 3.45/1.56  tff(c_722, plain, (![A_168, B_169, C_170]: (k1_relset_1(A_168, B_169, C_170)=k1_relat_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.45/1.56  tff(c_741, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_722])).
% 3.45/1.56  tff(c_755, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_741, c_38])).
% 3.45/1.56  tff(c_436, plain, (![C_126, A_127, B_128]: (v1_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.45/1.56  tff(c_445, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_436])).
% 3.45/1.56  tff(c_498, plain, (![C_143, B_144, A_145]: (v5_relat_1(C_143, B_144) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.56  tff(c_512, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_498])).
% 3.45/1.56  tff(c_491, plain, (![C_140, B_141, A_142]: (r2_hidden(C_140, B_141) | ~r2_hidden(C_140, A_142) | ~r1_tarski(A_142, B_141))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.45/1.56  tff(c_531, plain, (![A_153, B_154]: (r2_hidden('#skF_1'(A_153), B_154) | ~r1_tarski(A_153, B_154) | v1_xboole_0(A_153))), inference(resolution, [status(thm)], [c_4, c_491])).
% 3.45/1.56  tff(c_546, plain, (![A_153, B_154]: (m1_subset_1('#skF_1'(A_153), B_154) | ~r1_tarski(A_153, B_154) | v1_xboole_0(A_153))), inference(resolution, [status(thm)], [c_531, c_14])).
% 3.45/1.56  tff(c_601, plain, (![A_162, B_163, C_164]: (k2_relset_1(A_162, B_163, C_164)=k2_relat_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.56  tff(c_620, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_601])).
% 3.45/1.56  tff(c_59, plain, (![A_56]: (v1_xboole_0(A_56) | r2_hidden('#skF_1'(A_56), A_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.56  tff(c_70, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_59, c_36])).
% 3.45/1.56  tff(c_420, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_70])).
% 3.45/1.56  tff(c_622, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_620, c_420])).
% 3.45/1.56  tff(c_631, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_546, c_622])).
% 3.45/1.56  tff(c_665, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_631])).
% 3.45/1.56  tff(c_668, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_665])).
% 3.45/1.56  tff(c_675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_445, c_512, c_668])).
% 3.45/1.56  tff(c_676, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_631])).
% 3.45/1.56  tff(c_446, plain, (![A_129, B_130]: (r2_hidden('#skF_2'(A_129, B_130), A_129) | r1_tarski(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.45/1.56  tff(c_464, plain, (![A_129, B_130]: (~v1_xboole_0(A_129) | r1_tarski(A_129, B_130))), inference(resolution, [status(thm)], [c_446, c_2])).
% 3.45/1.56  tff(c_513, plain, (![B_146, A_147]: (v5_relat_1(B_146, A_147) | ~r1_tarski(k2_relat_1(B_146), A_147) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.45/1.56  tff(c_522, plain, (![B_146, B_130]: (v5_relat_1(B_146, B_130) | ~v1_relat_1(B_146) | ~v1_xboole_0(k2_relat_1(B_146)))), inference(resolution, [status(thm)], [c_464, c_513])).
% 3.45/1.56  tff(c_679, plain, (![B_130]: (v5_relat_1('#skF_5', B_130) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_676, c_522])).
% 3.45/1.56  tff(c_688, plain, (![B_130]: (v5_relat_1('#skF_5', B_130))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_679])).
% 3.45/1.56  tff(c_690, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_676, c_12])).
% 3.45/1.56  tff(c_704, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13) | ~v5_relat_1('#skF_5', A_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_690, c_18])).
% 3.45/1.56  tff(c_716, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_688, c_704])).
% 3.45/1.56  tff(c_796, plain, (![D_174, C_175, B_176, A_177]: (m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(C_175, B_176))) | ~r1_tarski(k2_relat_1(D_174), B_176) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(C_175, A_177))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.45/1.56  tff(c_807, plain, (![B_176]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_176))) | ~r1_tarski(k2_relat_1('#skF_5'), B_176))), inference(resolution, [status(thm)], [c_40, c_796])).
% 3.45/1.56  tff(c_819, plain, (![B_178]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_178))))), inference(demodulation, [status(thm), theory('equality')], [c_716, c_690, c_807])).
% 3.45/1.56  tff(c_28, plain, (![C_25, B_23, A_22]: (v1_xboole_0(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(B_23, A_22))) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.45/1.56  tff(c_846, plain, (![B_178]: (v1_xboole_0('#skF_5') | ~v1_xboole_0(B_178))), inference(resolution, [status(thm)], [c_819, c_28])).
% 3.45/1.56  tff(c_853, plain, (![B_178]: (~v1_xboole_0(B_178))), inference(splitLeft, [status(thm)], [c_846])).
% 3.45/1.56  tff(c_864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_853, c_410])).
% 3.45/1.56  tff(c_865, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_846])).
% 3.45/1.56  tff(c_51, plain, (![A_51]: (k1_relat_1(A_51)=k1_xboole_0 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_47, c_12])).
% 3.45/1.56  tff(c_868, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_865, c_51])).
% 3.45/1.56  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_755, c_868])).
% 3.45/1.56  tff(c_876, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_70])).
% 3.45/1.56  tff(c_899, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_876, c_12])).
% 3.45/1.56  tff(c_901, plain, (![D_47]: (~r2_hidden(D_47, k1_xboole_0) | ~m1_subset_1(D_47, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_36])).
% 3.45/1.56  tff(c_942, plain, (![B_186]: (~m1_subset_1('#skF_2'(k1_xboole_0, B_186), '#skF_4') | r1_tarski(k1_xboole_0, B_186))), inference(resolution, [status(thm)], [c_927, c_901])).
% 3.45/1.56  tff(c_1224, plain, (![B_234]: (~r1_tarski(k1_xboole_0, '#skF_4') | r1_tarski(k1_xboole_0, B_234))), inference(resolution, [status(thm)], [c_1190, c_942])).
% 3.45/1.56  tff(c_1226, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_1224])).
% 3.45/1.56  tff(c_1229, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_945, c_1226])).
% 3.45/1.56  tff(c_1233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_410, c_1229])).
% 3.45/1.56  tff(c_1234, plain, (![B_234]: (r1_tarski(k1_xboole_0, B_234))), inference(splitRight, [status(thm)], [c_1224])).
% 3.45/1.56  tff(c_1254, plain, (![A_237, B_238, C_239]: (k2_relset_1(A_237, B_238, C_239)=k2_relat_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.56  tff(c_1273, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1254])).
% 3.45/1.56  tff(c_1279, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_899, c_1273])).
% 3.45/1.56  tff(c_1366, plain, (![D_251, C_252, B_253, A_254]: (m1_subset_1(D_251, k1_zfmisc_1(k2_zfmisc_1(C_252, B_253))) | ~r1_tarski(k2_relat_1(D_251), B_253) | ~m1_subset_1(D_251, k1_zfmisc_1(k2_zfmisc_1(C_252, A_254))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.45/1.56  tff(c_1380, plain, (![B_253]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_253))) | ~r1_tarski(k2_relat_1('#skF_5'), B_253))), inference(resolution, [status(thm)], [c_40, c_1366])).
% 3.45/1.56  tff(c_1389, plain, (![B_255]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_255))))), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_1279, c_1380])).
% 3.45/1.56  tff(c_1416, plain, (![B_255]: (v1_xboole_0('#skF_5') | ~v1_xboole_0(B_255))), inference(resolution, [status(thm)], [c_1389, c_28])).
% 3.45/1.56  tff(c_1423, plain, (![B_255]: (~v1_xboole_0(B_255))), inference(splitLeft, [status(thm)], [c_1416])).
% 3.45/1.56  tff(c_1437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1423, c_410])).
% 3.45/1.56  tff(c_1438, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1416])).
% 3.45/1.56  tff(c_1449, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1438, c_51])).
% 3.45/1.56  tff(c_1456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1147, c_1449])).
% 3.45/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.56  
% 3.45/1.56  Inference rules
% 3.45/1.56  ----------------------
% 3.45/1.56  #Ref     : 0
% 3.45/1.56  #Sup     : 276
% 3.45/1.56  #Fact    : 0
% 3.45/1.56  #Define  : 0
% 3.45/1.56  #Split   : 6
% 3.45/1.56  #Chain   : 0
% 3.45/1.56  #Close   : 0
% 3.45/1.56  
% 3.45/1.56  Ordering : KBO
% 3.45/1.56  
% 3.45/1.56  Simplification rules
% 3.45/1.56  ----------------------
% 3.45/1.56  #Subsume      : 55
% 3.45/1.56  #Demod        : 125
% 3.45/1.56  #Tautology    : 93
% 3.45/1.56  #SimpNegUnit  : 32
% 3.45/1.56  #BackRed      : 35
% 3.45/1.56  
% 3.45/1.56  #Partial instantiations: 0
% 3.45/1.56  #Strategies tried      : 1
% 3.45/1.56  
% 3.45/1.56  Timing (in seconds)
% 3.45/1.56  ----------------------
% 3.45/1.57  Preprocessing        : 0.30
% 3.45/1.57  Parsing              : 0.16
% 3.45/1.57  CNF conversion       : 0.02
% 3.45/1.57  Main loop            : 0.44
% 3.45/1.57  Inferencing          : 0.17
% 3.45/1.57  Reduction            : 0.13
% 3.45/1.57  Demodulation         : 0.08
% 3.45/1.57  BG Simplification    : 0.02
% 3.45/1.57  Subsumption          : 0.08
% 3.45/1.57  Abstraction          : 0.02
% 3.45/1.57  MUC search           : 0.00
% 3.45/1.57  Cooper               : 0.00
% 3.45/1.57  Total                : 0.79
% 3.45/1.57  Index Insertion      : 0.00
% 3.45/1.57  Index Deletion       : 0.00
% 3.45/1.57  Index Matching       : 0.00
% 3.45/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
