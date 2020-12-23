%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0841+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:56 EST 2020

% Result     : Theorem 6.13s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :  232 ( 680 expanded)
%              Number of leaves         :   33 ( 234 expanded)
%              Depth                    :   10
%              Number of atoms          :  421 (1982 expanded)
%              Number of equality atoms :   12 (  40 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(F,E),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_44,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5722,plain,(
    ! [A_1055,B_1056,C_1057,D_1058] :
      ( k7_relset_1(A_1055,B_1056,C_1057,D_1058) = k9_relat_1(C_1057,D_1058)
      | ~ m1_subset_1(C_1057,k1_zfmisc_1(k2_zfmisc_1(A_1055,B_1056))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5732,plain,(
    ! [D_1058] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_1058) = k9_relat_1('#skF_9',D_1058) ),
    inference(resolution,[status(thm)],[c_42,c_5722])).

tff(c_2339,plain,(
    ! [A_531,B_532,C_533,D_534] :
      ( k7_relset_1(A_531,B_532,C_533,D_534) = k9_relat_1(C_533,D_534)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1(A_531,B_532))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2349,plain,(
    ! [D_534] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_534) = k9_relat_1('#skF_9',D_534) ),
    inference(resolution,[status(thm)],[c_42,c_2339])).

tff(c_375,plain,(
    ! [A_238,B_239,C_240,D_241] :
      ( k7_relset_1(A_238,B_239,C_240,D_241) = k9_relat_1(C_240,D_241)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_385,plain,(
    ! [D_241] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_241) = k9_relat_1('#skF_9',D_241) ),
    inference(resolution,[status(thm)],[c_42,c_375])).

tff(c_64,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_102,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_56,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_77,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_60,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_111,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_86,plain,(
    ! [C_161,A_162,B_163] :
      ( v1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_94,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_86])).

tff(c_195,plain,(
    ! [D_200,A_201,B_202,E_203] :
      ( r2_hidden(D_200,k9_relat_1(A_201,B_202))
      | ~ r2_hidden(E_203,B_202)
      | ~ r2_hidden(k4_tarski(E_203,D_200),A_201)
      | ~ v1_relat_1(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_208,plain,(
    ! [D_204,A_205] :
      ( r2_hidden(D_204,k9_relat_1(A_205,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_11',D_204),A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(resolution,[status(thm)],[c_77,c_195])).

tff(c_215,plain,
    ( r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_111,c_208])).

tff(c_223,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_215])).

tff(c_173,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k7_relset_1(A_195,B_196,C_197,D_198) = k9_relat_1(C_197,D_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_183,plain,(
    ! [D_198] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_198) = k9_relat_1('#skF_9',D_198) ),
    inference(resolution,[status(thm)],[c_42,c_173])).

tff(c_50,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | ~ r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_295,plain,(
    ! [F_215] :
      ( ~ r2_hidden(F_215,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_215,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_215,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_183,c_50])).

tff(c_298,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_111,c_295])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_77,c_298])).

tff(c_306,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_389,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_306])).

tff(c_1245,plain,(
    ! [A_386,B_387,D_388] :
      ( r2_hidden(k4_tarski('#skF_4'(A_386,B_387,k9_relat_1(A_386,B_387),D_388),D_388),A_386)
      | ~ r2_hidden(D_388,k9_relat_1(A_386,B_387))
      | ~ v1_relat_1(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(A_58,B_59)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_103,plain,(
    ! [A_170,C_171,B_172] :
      ( m1_subset_1(A_170,C_171)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(C_171))
      | ~ r2_hidden(A_170,B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_109,plain,(
    ! [A_170] :
      ( m1_subset_1(A_170,k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(A_170,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_42,c_103])).

tff(c_321,plain,(
    ! [B_216,D_217,A_218,C_219] :
      ( r2_hidden(B_216,D_217)
      | ~ r2_hidden(k4_tarski(A_218,B_216),k2_zfmisc_1(C_219,D_217)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_440,plain,(
    ! [B_251,D_252,C_253,A_254] :
      ( r2_hidden(B_251,D_252)
      | v1_xboole_0(k2_zfmisc_1(C_253,D_252))
      | ~ m1_subset_1(k4_tarski(A_254,B_251),k2_zfmisc_1(C_253,D_252)) ) ),
    inference(resolution,[status(thm)],[c_34,c_321])).

tff(c_449,plain,(
    ! [B_251,A_254] :
      ( r2_hidden(B_251,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_254,B_251),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_109,c_440])).

tff(c_450,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_355,plain,(
    ! [A_226,B_227,C_228,D_229] :
      ( r2_hidden(k4_tarski(A_226,B_227),k2_zfmisc_1(C_228,D_229))
      | ~ r2_hidden(B_227,D_229)
      | ~ r2_hidden(A_226,C_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    ! [B_64,A_63] :
      ( ~ v1_xboole_0(B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_371,plain,(
    ! [C_228,D_229,B_227,A_226] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_228,D_229))
      | ~ r2_hidden(B_227,D_229)
      | ~ r2_hidden(A_226,C_228) ) ),
    inference(resolution,[status(thm)],[c_355,c_38])).

tff(c_455,plain,(
    ! [B_227,A_226] :
      ( ~ r2_hidden(B_227,'#skF_6')
      | ~ r2_hidden(A_226,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_450,c_371])).

tff(c_457,plain,(
    ! [A_255] : ~ r2_hidden(A_255,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_461,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_58,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_457])).

tff(c_464,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_461])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_464,c_102])).

tff(c_468,plain,(
    ! [B_256] : ~ r2_hidden(B_256,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_472,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_468])).

tff(c_475,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_472])).

tff(c_40,plain,(
    m1_subset_1('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_40])).

tff(c_501,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_97,plain,(
    ! [A_166,C_167,B_168,D_169] :
      ( r2_hidden(A_166,C_167)
      | ~ r2_hidden(k4_tarski(A_166,B_168),k2_zfmisc_1(C_167,D_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_854,plain,(
    ! [A_309,C_310,D_311,B_312] :
      ( r2_hidden(A_309,C_310)
      | v1_xboole_0(k2_zfmisc_1(C_310,D_311))
      | ~ m1_subset_1(k4_tarski(A_309,B_312),k2_zfmisc_1(C_310,D_311)) ) ),
    inference(resolution,[status(thm)],[c_34,c_97])).

tff(c_861,plain,(
    ! [A_309,B_312] :
      ( r2_hidden(A_309,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_309,B_312),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_109,c_854])).

tff(c_865,plain,(
    ! [A_309,B_312] :
      ( r2_hidden(A_309,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_309,B_312),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_861])).

tff(c_1261,plain,(
    ! [B_387,D_388] :
      ( r2_hidden('#skF_4'('#skF_9',B_387,k9_relat_1('#skF_9',B_387),D_388),'#skF_8')
      | ~ r2_hidden(D_388,k9_relat_1('#skF_9',B_387))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1245,c_865])).

tff(c_1938,plain,(
    ! [B_450,D_451] :
      ( r2_hidden('#skF_4'('#skF_9',B_450,k9_relat_1('#skF_9',B_450),D_451),'#skF_8')
      | ~ r2_hidden(D_451,k9_relat_1('#skF_9',B_450)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1261])).

tff(c_32,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(A_56,B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1992,plain,(
    ! [B_461,D_462] :
      ( m1_subset_1('#skF_4'('#skF_9',B_461,k9_relat_1('#skF_9',B_461),D_462),'#skF_8')
      | ~ r2_hidden(D_462,k9_relat_1('#skF_9',B_461)) ) ),
    inference(resolution,[status(thm)],[c_1938,c_32])).

tff(c_6,plain,(
    ! [A_4,B_27,D_42] :
      ( r2_hidden('#skF_4'(A_4,B_27,k9_relat_1(A_4,B_27),D_42),B_27)
      | ~ r2_hidden(D_42,k9_relat_1(A_4,B_27))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_307,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_399,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_58])).

tff(c_1271,plain,(
    ! [B_387] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_387,k9_relat_1('#skF_9',B_387),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_387,k9_relat_1('#skF_9',B_387),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_387))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1245,c_399])).

tff(c_1950,plain,(
    ! [B_452] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_452,k9_relat_1('#skF_9',B_452),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_452,k9_relat_1('#skF_9',B_452),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_452)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1271])).

tff(c_1954,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k9_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_1950])).

tff(c_1960,plain,(
    ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k9_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_389,c_1954])).

tff(c_1995,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1992,c_1960])).

tff(c_1999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_1995])).

tff(c_2001,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2002,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_22,plain,(
    ! [A_46] : m1_subset_1('#skF_5'(A_46),A_46) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2019,plain,(
    ! [A_463,C_464,B_465] :
      ( m1_subset_1(A_463,C_464)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(C_464))
      | ~ r2_hidden(A_463,B_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2025,plain,(
    ! [A_463] :
      ( m1_subset_1(A_463,k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(A_463,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_42,c_2019])).

tff(c_2135,plain,(
    ! [A_495,C_496,D_497,B_498] :
      ( r2_hidden(A_495,C_496)
      | v1_xboole_0(k2_zfmisc_1(C_496,D_497))
      | ~ m1_subset_1(k4_tarski(A_495,B_498),k2_zfmisc_1(C_496,D_497)) ) ),
    inference(resolution,[status(thm)],[c_34,c_97])).

tff(c_2144,plain,(
    ! [A_495,B_498] :
      ( r2_hidden(A_495,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_495,B_498),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2025,c_2135])).

tff(c_2178,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2144])).

tff(c_2061,plain,(
    ! [A_476,B_477,C_478,D_479] :
      ( r2_hidden(k4_tarski(A_476,B_477),k2_zfmisc_1(C_478,D_479))
      | ~ r2_hidden(B_477,D_479)
      | ~ r2_hidden(A_476,C_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2077,plain,(
    ! [C_478,D_479,B_477,A_476] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_478,D_479))
      | ~ r2_hidden(B_477,D_479)
      | ~ r2_hidden(A_476,C_478) ) ),
    inference(resolution,[status(thm)],[c_2061,c_38])).

tff(c_2181,plain,(
    ! [B_477,A_476] :
      ( ~ r2_hidden(B_477,'#skF_6')
      | ~ r2_hidden(A_476,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2178,c_2077])).

tff(c_2185,plain,(
    ! [A_505] : ~ r2_hidden(A_505,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2181])).

tff(c_2189,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_58,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_2185])).

tff(c_2193,plain,(
    ! [A_506] : ~ m1_subset_1(A_506,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2189])).

tff(c_2203,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_2193])).

tff(c_2205,plain,(
    ! [B_507] : ~ r2_hidden(B_507,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2181])).

tff(c_2209,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_2205])).

tff(c_2212,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2209])).

tff(c_2214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2212,c_40])).

tff(c_2234,plain,(
    ! [A_511,B_512] :
      ( r2_hidden(A_511,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_511,B_512),'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_2144])).

tff(c_2241,plain,(
    r2_hidden('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_2002,c_2234])).

tff(c_2249,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_2241,c_32])).

tff(c_2257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2001,c_2249])).

tff(c_2258,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2353,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2349,c_2258])).

tff(c_3511,plain,(
    ! [A_725,B_726,D_727] :
      ( r2_hidden(k4_tarski('#skF_4'(A_725,B_726,k9_relat_1(A_725,B_726),D_727),D_727),A_725)
      | ~ r2_hidden(D_727,k9_relat_1(A_725,B_726))
      | ~ v1_relat_1(A_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2280,plain,(
    ! [A_514,C_515,B_516] :
      ( m1_subset_1(A_514,C_515)
      | ~ m1_subset_1(B_516,k1_zfmisc_1(C_515))
      | ~ r2_hidden(A_514,B_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2286,plain,(
    ! [A_514] :
      ( m1_subset_1(A_514,k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(A_514,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_42,c_2280])).

tff(c_2296,plain,(
    ! [B_520,D_521,A_522,C_523] :
      ( r2_hidden(B_520,D_521)
      | ~ r2_hidden(k4_tarski(A_522,B_520),k2_zfmisc_1(C_523,D_521)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2401,plain,(
    ! [B_551,D_552,C_553,A_554] :
      ( r2_hidden(B_551,D_552)
      | v1_xboole_0(k2_zfmisc_1(C_553,D_552))
      | ~ m1_subset_1(k4_tarski(A_554,B_551),k2_zfmisc_1(C_553,D_552)) ) ),
    inference(resolution,[status(thm)],[c_34,c_2296])).

tff(c_2410,plain,(
    ! [B_551,A_554] :
      ( r2_hidden(B_551,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_554,B_551),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2286,c_2401])).

tff(c_2411,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2410])).

tff(c_2322,plain,(
    ! [A_527,B_528,C_529,D_530] :
      ( r2_hidden(k4_tarski(A_527,B_528),k2_zfmisc_1(C_529,D_530))
      | ~ r2_hidden(B_528,D_530)
      | ~ r2_hidden(A_527,C_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2338,plain,(
    ! [C_529,D_530,B_528,A_527] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_529,D_530))
      | ~ r2_hidden(B_528,D_530)
      | ~ r2_hidden(A_527,C_529) ) ),
    inference(resolution,[status(thm)],[c_2322,c_38])).

tff(c_2416,plain,(
    ! [B_528,A_527] :
      ( ~ r2_hidden(B_528,'#skF_6')
      | ~ r2_hidden(A_527,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2411,c_2338])).

tff(c_2418,plain,(
    ! [A_555] : ~ r2_hidden(A_555,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2416])).

tff(c_2422,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_58,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_2418])).

tff(c_2426,plain,(
    ! [A_556] : ~ m1_subset_1(A_556,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2422])).

tff(c_2436,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_2426])).

tff(c_2438,plain,(
    ! [B_557] : ~ r2_hidden(B_557,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2416])).

tff(c_2442,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_2438])).

tff(c_2445,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2442])).

tff(c_2469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2445,c_40])).

tff(c_2471,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2410])).

tff(c_3064,plain,(
    ! [A_640,C_641,D_642,B_643] :
      ( r2_hidden(A_640,C_641)
      | v1_xboole_0(k2_zfmisc_1(C_641,D_642))
      | ~ m1_subset_1(k4_tarski(A_640,B_643),k2_zfmisc_1(C_641,D_642)) ) ),
    inference(resolution,[status(thm)],[c_34,c_97])).

tff(c_3071,plain,(
    ! [A_640,B_643] :
      ( r2_hidden(A_640,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_640,B_643),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2286,c_3064])).

tff(c_3075,plain,(
    ! [A_640,B_643] :
      ( r2_hidden(A_640,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_640,B_643),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2471,c_3071])).

tff(c_3527,plain,(
    ! [B_726,D_727] :
      ( r2_hidden('#skF_4'('#skF_9',B_726,k9_relat_1('#skF_9',B_726),D_727),'#skF_8')
      | ~ r2_hidden(D_727,k9_relat_1('#skF_9',B_726))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3511,c_3075])).

tff(c_3997,plain,(
    ! [B_766,D_767] :
      ( r2_hidden('#skF_4'('#skF_9',B_766,k9_relat_1('#skF_9',B_766),D_767),'#skF_8')
      | ~ r2_hidden(D_767,k9_relat_1('#skF_9',B_766)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3527])).

tff(c_4221,plain,(
    ! [B_790,D_791] :
      ( m1_subset_1('#skF_4'('#skF_9',B_790,k9_relat_1('#skF_9',B_790),D_791),'#skF_8')
      | ~ r2_hidden(D_791,k9_relat_1('#skF_9',B_790)) ) ),
    inference(resolution,[status(thm)],[c_3997,c_32])).

tff(c_62,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2260,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2001,c_62])).

tff(c_3545,plain,(
    ! [B_726] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_726,k9_relat_1('#skF_9',B_726),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_726,k9_relat_1('#skF_9',B_726),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_726))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3511,c_2260])).

tff(c_3699,plain,(
    ! [B_733] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_733,k9_relat_1('#skF_9',B_733),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_733,k9_relat_1('#skF_9',B_733),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_733)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3545])).

tff(c_3703,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k9_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_3699])).

tff(c_3709,plain,(
    ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k9_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2353,c_3703])).

tff(c_4224,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4221,c_3709])).

tff(c_4228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2353,c_4224])).

tff(c_4229,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5736,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5732,c_4229])).

tff(c_4245,plain,(
    ! [C_792,A_793,B_794] :
      ( v1_relat_1(C_792)
      | ~ m1_subset_1(C_792,k1_zfmisc_1(k2_zfmisc_1(A_793,B_794))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_4253,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_4245])).

tff(c_6390,plain,(
    ! [A_1202,B_1203,D_1204] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1202,B_1203,k9_relat_1(A_1202,B_1203),D_1204),D_1204),A_1202)
      | ~ r2_hidden(D_1204,k9_relat_1(A_1202,B_1203))
      | ~ v1_relat_1(A_1202) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4262,plain,(
    ! [A_801,C_802,B_803] :
      ( m1_subset_1(A_801,C_802)
      | ~ m1_subset_1(B_803,k1_zfmisc_1(C_802))
      | ~ r2_hidden(A_801,B_803) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4268,plain,(
    ! [A_801] :
      ( m1_subset_1(A_801,k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(A_801,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_42,c_4262])).

tff(c_4271,plain,(
    ! [B_805,D_806,A_807,C_808] :
      ( r2_hidden(B_805,D_806)
      | ~ r2_hidden(k4_tarski(A_807,B_805),k2_zfmisc_1(C_808,D_806)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5756,plain,(
    ! [B_1064,D_1065,C_1066,A_1067] :
      ( r2_hidden(B_1064,D_1065)
      | v1_xboole_0(k2_zfmisc_1(C_1066,D_1065))
      | ~ m1_subset_1(k4_tarski(A_1067,B_1064),k2_zfmisc_1(C_1066,D_1065)) ) ),
    inference(resolution,[status(thm)],[c_34,c_4271])).

tff(c_5765,plain,(
    ! [B_1064,A_1067] :
      ( r2_hidden(B_1064,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_1067,B_1064),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4268,c_5756])).

tff(c_5766,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5765])).

tff(c_5702,plain,(
    ! [A_1046,B_1047,C_1048,D_1049] :
      ( r2_hidden(k4_tarski(A_1046,B_1047),k2_zfmisc_1(C_1048,D_1049))
      | ~ r2_hidden(B_1047,D_1049)
      | ~ r2_hidden(A_1046,C_1048) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5718,plain,(
    ! [C_1048,D_1049,B_1047,A_1046] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_1048,D_1049))
      | ~ r2_hidden(B_1047,D_1049)
      | ~ r2_hidden(A_1046,C_1048) ) ),
    inference(resolution,[status(thm)],[c_5702,c_38])).

tff(c_5769,plain,(
    ! [B_1047,A_1046] :
      ( ~ r2_hidden(B_1047,'#skF_6')
      | ~ r2_hidden(A_1046,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5766,c_5718])).

tff(c_5781,plain,(
    ! [A_1072] : ~ r2_hidden(A_1072,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5769])).

tff(c_5785,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_58,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_5781])).

tff(c_5788,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_5785])).

tff(c_4329,plain,(
    ! [A_827,B_828,C_829,D_830] :
      ( k7_relset_1(A_827,B_828,C_829,D_830) = k9_relat_1(C_829,D_830)
      | ~ m1_subset_1(C_829,k1_zfmisc_1(k2_zfmisc_1(A_827,B_828))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4339,plain,(
    ! [D_830] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_830) = k9_relat_1('#skF_9',D_830) ),
    inference(resolution,[status(thm)],[c_42,c_4329])).

tff(c_4343,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4339,c_4229])).

tff(c_4897,plain,(
    ! [A_935,B_936,D_937] :
      ( r2_hidden(k4_tarski('#skF_4'(A_935,B_936,k9_relat_1(A_935,B_936),D_937),D_937),A_935)
      | ~ r2_hidden(D_937,k9_relat_1(A_935,B_936))
      | ~ v1_relat_1(A_935) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4365,plain,(
    ! [B_833,D_834,C_835,A_836] :
      ( r2_hidden(B_833,D_834)
      | v1_xboole_0(k2_zfmisc_1(C_835,D_834))
      | ~ m1_subset_1(k4_tarski(A_836,B_833),k2_zfmisc_1(C_835,D_834)) ) ),
    inference(resolution,[status(thm)],[c_34,c_4271])).

tff(c_4374,plain,(
    ! [B_833,A_836] :
      ( r2_hidden(B_833,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_836,B_833),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4268,c_4365])).

tff(c_4375,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4374])).

tff(c_4310,plain,(
    ! [A_815,B_816,C_817,D_818] :
      ( r2_hidden(k4_tarski(A_815,B_816),k2_zfmisc_1(C_817,D_818))
      | ~ r2_hidden(B_816,D_818)
      | ~ r2_hidden(A_815,C_817) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4326,plain,(
    ! [C_817,D_818,B_816,A_815] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_817,D_818))
      | ~ r2_hidden(B_816,D_818)
      | ~ r2_hidden(A_815,C_817) ) ),
    inference(resolution,[status(thm)],[c_4310,c_38])).

tff(c_4388,plain,(
    ! [B_816,A_815] :
      ( ~ r2_hidden(B_816,'#skF_6')
      | ~ r2_hidden(A_815,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4375,c_4326])).

tff(c_4390,plain,(
    ! [A_841] : ~ r2_hidden(A_841,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4388])).

tff(c_4394,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_58,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_4390])).

tff(c_4398,plain,(
    ! [A_842] : ~ m1_subset_1(A_842,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_4394])).

tff(c_4408,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_4398])).

tff(c_4410,plain,(
    ! [B_843] : ~ r2_hidden(B_843,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_4388])).

tff(c_4414,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_4410])).

tff(c_4417,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4414])).

tff(c_4419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4417,c_40])).

tff(c_4421,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4374])).

tff(c_4257,plain,(
    ! [A_797,C_798,B_799,D_800] :
      ( r2_hidden(A_797,C_798)
      | ~ r2_hidden(k4_tarski(A_797,B_799),k2_zfmisc_1(C_798,D_800)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4855,plain,(
    ! [A_925,C_926,D_927,B_928] :
      ( r2_hidden(A_925,C_926)
      | v1_xboole_0(k2_zfmisc_1(C_926,D_927))
      | ~ m1_subset_1(k4_tarski(A_925,B_928),k2_zfmisc_1(C_926,D_927)) ) ),
    inference(resolution,[status(thm)],[c_34,c_4257])).

tff(c_4862,plain,(
    ! [A_925,B_928] :
      ( r2_hidden(A_925,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_925,B_928),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4268,c_4855])).

tff(c_4866,plain,(
    ! [A_925,B_928] :
      ( r2_hidden(A_925,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_925,B_928),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4421,c_4862])).

tff(c_4901,plain,(
    ! [B_936,D_937] :
      ( r2_hidden('#skF_4'('#skF_9',B_936,k9_relat_1('#skF_9',B_936),D_937),'#skF_8')
      | ~ r2_hidden(D_937,k9_relat_1('#skF_9',B_936))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4897,c_4866])).

tff(c_5636,plain,(
    ! [B_1032,D_1033] :
      ( r2_hidden('#skF_4'('#skF_9',B_1032,k9_relat_1('#skF_9',B_1032),D_1033),'#skF_8')
      | ~ r2_hidden(D_1033,k9_relat_1('#skF_9',B_1032)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_4901])).

tff(c_5672,plain,(
    ! [B_1042,D_1043] :
      ( m1_subset_1('#skF_4'('#skF_9',B_1042,k9_relat_1('#skF_9',B_1042),D_1043),'#skF_8')
      | ~ r2_hidden(D_1043,k9_relat_1('#skF_9',B_1042)) ) ),
    inference(resolution,[status(thm)],[c_5636,c_32])).

tff(c_4289,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_4919,plain,(
    ! [B_936] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_936,k9_relat_1('#skF_9',B_936),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_936,k9_relat_1('#skF_9',B_936),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_936))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4897,c_4289])).

tff(c_5206,plain,(
    ! [B_963] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_963,k9_relat_1('#skF_9',B_963),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_963,k9_relat_1('#skF_9',B_963),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_963)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_4919])).

tff(c_5210,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k9_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_5206])).

tff(c_5216,plain,(
    ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k9_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_4343,c_5210])).

tff(c_5675,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_5672,c_5216])).

tff(c_5679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4343,c_5675])).

tff(c_5680,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_5790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5788,c_5680])).

tff(c_5794,plain,(
    ! [B_1073] : ~ r2_hidden(B_1073,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_5769])).

tff(c_5798,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_5794])).

tff(c_5801,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_5798])).

tff(c_5803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5801,c_40])).

tff(c_5805,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5765])).

tff(c_6171,plain,(
    ! [A_1143,C_1144,D_1145,B_1146] :
      ( r2_hidden(A_1143,C_1144)
      | v1_xboole_0(k2_zfmisc_1(C_1144,D_1145))
      | ~ m1_subset_1(k4_tarski(A_1143,B_1146),k2_zfmisc_1(C_1144,D_1145)) ) ),
    inference(resolution,[status(thm)],[c_34,c_4257])).

tff(c_6178,plain,(
    ! [A_1143,B_1146] :
      ( r2_hidden(A_1143,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_1143,B_1146),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4268,c_6171])).

tff(c_6182,plain,(
    ! [A_1143,B_1146] :
      ( r2_hidden(A_1143,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_1143,B_1146),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5805,c_6178])).

tff(c_6416,plain,(
    ! [B_1203,D_1204] :
      ( r2_hidden('#skF_4'('#skF_9',B_1203,k9_relat_1('#skF_9',B_1203),D_1204),'#skF_8')
      | ~ r2_hidden(D_1204,k9_relat_1('#skF_9',B_1203))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6390,c_6182])).

tff(c_7065,plain,(
    ! [B_1274,D_1275] :
      ( r2_hidden('#skF_4'('#skF_9',B_1274,k9_relat_1('#skF_9',B_1274),D_1275),'#skF_8')
      | ~ r2_hidden(D_1275,k9_relat_1('#skF_9',B_1274)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_6416])).

tff(c_7097,plain,(
    ! [B_1284,D_1285] :
      ( m1_subset_1('#skF_4'('#skF_9',B_1284,k9_relat_1('#skF_9',B_1284),D_1285),'#skF_8')
      | ~ r2_hidden(D_1285,k9_relat_1('#skF_9',B_1284)) ) ),
    inference(resolution,[status(thm)],[c_7065,c_32])).

tff(c_4230,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5681,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4230,c_54])).

tff(c_6424,plain,(
    ! [B_1203] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_1203,k9_relat_1('#skF_9',B_1203),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_1203,k9_relat_1('#skF_9',B_1203),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_1203))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6390,c_5681])).

tff(c_6529,plain,(
    ! [B_1210] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_1210,k9_relat_1('#skF_9',B_1210),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_1210,k9_relat_1('#skF_9',B_1210),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_1210)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_6424])).

tff(c_6533,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k9_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_6529])).

tff(c_6539,plain,(
    ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k9_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_5736,c_6533])).

tff(c_7100,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_7097,c_6539])).

tff(c_7104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5736,c_7100])).

%------------------------------------------------------------------------------
