%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0842+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:56 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 644 expanded)
%              Number of leaves         :   33 ( 222 expanded)
%              Depth                    :    9
%              Number of atoms          :  394 (1874 expanded)
%              Number of equality atoms :   12 (  40 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k8_relset_1(A,C,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(E,F),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_44,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6468,plain,(
    ! [A_1132,B_1133,C_1134,D_1135] :
      ( k8_relset_1(A_1132,B_1133,C_1134,D_1135) = k10_relat_1(C_1134,D_1135)
      | ~ m1_subset_1(C_1134,k1_zfmisc_1(k2_zfmisc_1(A_1132,B_1133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6478,plain,(
    ! [D_1135] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_1135) = k10_relat_1('#skF_9',D_1135) ),
    inference(resolution,[status(thm)],[c_42,c_6468])).

tff(c_2575,plain,(
    ! [A_579,B_580,C_581,D_582] :
      ( k8_relset_1(A_579,B_580,C_581,D_582) = k10_relat_1(C_581,D_582)
      | ~ m1_subset_1(C_581,k1_zfmisc_1(k2_zfmisc_1(A_579,B_580))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2585,plain,(
    ! [D_582] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_582) = k10_relat_1('#skF_9',D_582) ),
    inference(resolution,[status(thm)],[c_42,c_2575])).

tff(c_375,plain,(
    ! [A_238,B_239,C_240,D_241] :
      ( k8_relset_1(A_238,B_239,C_240,D_241) = k10_relat_1(C_240,D_241)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_385,plain,(
    ! [D_241] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_241) = k10_relat_1('#skF_9',D_241) ),
    inference(resolution,[status(thm)],[c_42,c_375])).

tff(c_64,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_102,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_56,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_77,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_60,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_111,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
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
      ( r2_hidden(D_200,k10_relat_1(A_201,B_202))
      | ~ r2_hidden(E_203,B_202)
      | ~ r2_hidden(k4_tarski(D_200,E_203),A_201)
      | ~ v1_relat_1(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_208,plain,(
    ! [D_204,A_205] :
      ( r2_hidden(D_204,k10_relat_1(A_205,'#skF_7'))
      | ~ r2_hidden(k4_tarski(D_204,'#skF_11'),A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(resolution,[status(thm)],[c_77,c_195])).

tff(c_215,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_111,c_208])).

tff(c_223,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_215])).

tff(c_173,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k8_relset_1(A_195,B_196,C_197,D_198) = k10_relat_1(C_197,D_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_183,plain,(
    ! [D_198] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_198) = k10_relat_1('#skF_9',D_198) ),
    inference(resolution,[status(thm)],[c_42,c_173])).

tff(c_50,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_295,plain,(
    ! [F_215] :
      ( ~ r2_hidden(F_215,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_215),'#skF_9')
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
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_389,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_306])).

tff(c_1245,plain,(
    ! [D_386,A_387,B_388] :
      ( r2_hidden(k4_tarski(D_386,'#skF_4'(A_387,B_388,k10_relat_1(A_387,B_388),D_386)),A_387)
      | ~ r2_hidden(D_386,k10_relat_1(A_387,B_388))
      | ~ v1_relat_1(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(A_58,B_59)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_103,plain,(
    ! [A_170,C_171,B_172] :
      ( m1_subset_1(A_170,C_171)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(C_171))
      | ~ r2_hidden(A_170,B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_109,plain,(
    ! [A_170] :
      ( m1_subset_1(A_170,k2_zfmisc_1('#skF_6','#skF_8'))
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
      ( r2_hidden(B_251,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(A_254,B_251),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_109,c_440])).

tff(c_450,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8')) ),
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
      ( ~ r2_hidden(B_227,'#skF_8')
      | ~ r2_hidden(A_226,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_450,c_371])).

tff(c_457,plain,(
    ! [A_255] : ~ r2_hidden(A_255,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_461,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_457])).

tff(c_464,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_461])).

tff(c_40,plain,(
    m1_subset_1('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_464,c_40])).

tff(c_468,plain,(
    ! [B_256] : ~ r2_hidden(B_256,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_472,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_58,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_468])).

tff(c_475,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_472])).

tff(c_499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_102])).

tff(c_500,plain,(
    ! [B_251,A_254] :
      ( r2_hidden(B_251,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_254,B_251),'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_1265,plain,(
    ! [B_388,D_386] :
      ( r2_hidden('#skF_4'('#skF_9',B_388,k10_relat_1('#skF_9',B_388),D_386),'#skF_8')
      | ~ r2_hidden(D_386,k10_relat_1('#skF_9',B_388))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1245,c_500])).

tff(c_1938,plain,(
    ! [B_450,D_451] :
      ( r2_hidden('#skF_4'('#skF_9',B_450,k10_relat_1('#skF_9',B_450),D_451),'#skF_8')
      | ~ r2_hidden(D_451,k10_relat_1('#skF_9',B_450)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1265])).

tff(c_32,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(A_56,B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1992,plain,(
    ! [B_461,D_462] :
      ( m1_subset_1('#skF_4'('#skF_9',B_461,k10_relat_1('#skF_9',B_461),D_462),'#skF_8')
      | ~ r2_hidden(D_462,k10_relat_1('#skF_9',B_461)) ) ),
    inference(resolution,[status(thm)],[c_1938,c_32])).

tff(c_6,plain,(
    ! [A_4,B_27,D_42] :
      ( r2_hidden('#skF_4'(A_4,B_27,k10_relat_1(A_4,B_27),D_42),B_27)
      | ~ r2_hidden(D_42,k10_relat_1(A_4,B_27))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_307,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_399,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_58])).

tff(c_1271,plain,(
    ! [B_388] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_388,k10_relat_1('#skF_9',B_388),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_388,k10_relat_1('#skF_9',B_388),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_388))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1245,c_399])).

tff(c_1950,plain,(
    ! [B_452] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_452,k10_relat_1('#skF_9',B_452),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_452,k10_relat_1('#skF_9',B_452),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_452)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1271])).

tff(c_1954,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k10_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_1950])).

tff(c_1960,plain,(
    ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k10_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_389,c_1954])).

tff(c_1995,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1992,c_1960])).

tff(c_1999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_1995])).

tff(c_2001,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2002,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
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
      ( m1_subset_1(A_463,k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(A_463,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_42,c_2019])).

tff(c_97,plain,(
    ! [A_166,C_167,B_168,D_169] :
      ( r2_hidden(A_166,C_167)
      | ~ r2_hidden(k4_tarski(A_166,B_168),k2_zfmisc_1(C_167,D_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2135,plain,(
    ! [A_495,C_496,D_497,B_498] :
      ( r2_hidden(A_495,C_496)
      | v1_xboole_0(k2_zfmisc_1(C_496,D_497))
      | ~ m1_subset_1(k4_tarski(A_495,B_498),k2_zfmisc_1(C_496,D_497)) ) ),
    inference(resolution,[status(thm)],[c_34,c_97])).

tff(c_2144,plain,(
    ! [A_495,B_498] :
      ( r2_hidden(A_495,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(A_495,B_498),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2025,c_2135])).

tff(c_2178,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8')) ),
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
      ( ~ r2_hidden(B_477,'#skF_8')
      | ~ r2_hidden(A_476,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2178,c_2077])).

tff(c_2185,plain,(
    ! [A_505] : ~ r2_hidden(A_505,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2181])).

tff(c_2189,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_2185])).

tff(c_2192,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2189])).

tff(c_2194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2192,c_40])).

tff(c_2196,plain,(
    ! [B_506] : ~ r2_hidden(B_506,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2181])).

tff(c_2200,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_58,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_2196])).

tff(c_2204,plain,(
    ! [A_507] : ~ m1_subset_1(A_507,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2200])).

tff(c_2214,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_2204])).

tff(c_2216,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2144])).

tff(c_2035,plain,(
    ! [B_469,D_470,A_471,C_472] :
      ( r2_hidden(B_469,D_470)
      | ~ r2_hidden(k4_tarski(A_471,B_469),k2_zfmisc_1(C_472,D_470)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2454,plain,(
    ! [B_546,D_547,C_548,A_549] :
      ( r2_hidden(B_546,D_547)
      | v1_xboole_0(k2_zfmisc_1(C_548,D_547))
      | ~ m1_subset_1(k4_tarski(A_549,B_546),k2_zfmisc_1(C_548,D_547)) ) ),
    inference(resolution,[status(thm)],[c_34,c_2035])).

tff(c_2461,plain,(
    ! [B_546,A_549] :
      ( r2_hidden(B_546,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(A_549,B_546),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2025,c_2454])).

tff(c_2466,plain,(
    ! [B_550,A_551] :
      ( r2_hidden(B_550,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_551,B_550),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2216,c_2461])).

tff(c_2473,plain,(
    r2_hidden('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_2002,c_2466])).

tff(c_2481,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_2473,c_32])).

tff(c_2489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2001,c_2481])).

tff(c_2490,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2589,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2585,c_2490])).

tff(c_3489,plain,(
    ! [D_726,A_727,B_728] :
      ( r2_hidden(k4_tarski(D_726,'#skF_4'(A_727,B_728,k10_relat_1(A_727,B_728),D_726)),A_727)
      | ~ r2_hidden(D_726,k10_relat_1(A_727,B_728))
      | ~ v1_relat_1(A_727) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2512,plain,(
    ! [A_556,C_557,B_558] :
      ( m1_subset_1(A_556,C_557)
      | ~ m1_subset_1(B_558,k1_zfmisc_1(C_557))
      | ~ r2_hidden(A_556,B_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2518,plain,(
    ! [A_556] :
      ( m1_subset_1(A_556,k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(A_556,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_42,c_2512])).

tff(c_2507,plain,(
    ! [B_552,D_553,A_554,C_555] :
      ( r2_hidden(B_552,D_553)
      | ~ r2_hidden(k4_tarski(A_554,B_552),k2_zfmisc_1(C_555,D_553)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2609,plain,(
    ! [B_584,D_585,C_586,A_587] :
      ( r2_hidden(B_584,D_585)
      | v1_xboole_0(k2_zfmisc_1(C_586,D_585))
      | ~ m1_subset_1(k4_tarski(A_587,B_584),k2_zfmisc_1(C_586,D_585)) ) ),
    inference(resolution,[status(thm)],[c_34,c_2507])).

tff(c_2618,plain,(
    ! [B_584,A_587] :
      ( r2_hidden(B_584,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(A_587,B_584),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2518,c_2609])).

tff(c_2619,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2618])).

tff(c_2520,plain,(
    ! [A_559,B_560,C_561,D_562] :
      ( r2_hidden(k4_tarski(A_559,B_560),k2_zfmisc_1(C_561,D_562))
      | ~ r2_hidden(B_560,D_562)
      | ~ r2_hidden(A_559,C_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2536,plain,(
    ! [C_561,D_562,B_560,A_559] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_561,D_562))
      | ~ r2_hidden(B_560,D_562)
      | ~ r2_hidden(A_559,C_561) ) ),
    inference(resolution,[status(thm)],[c_2520,c_38])).

tff(c_2622,plain,(
    ! [B_560,A_559] :
      ( ~ r2_hidden(B_560,'#skF_8')
      | ~ r2_hidden(A_559,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2619,c_2536])).

tff(c_2637,plain,(
    ! [A_592] : ~ r2_hidden(A_592,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2622])).

tff(c_2641,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_2637])).

tff(c_2644,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2641])).

tff(c_2646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2644,c_40])).

tff(c_2648,plain,(
    ! [B_593] : ~ r2_hidden(B_593,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2622])).

tff(c_2652,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_58,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_2648])).

tff(c_2658,plain,(
    ! [A_594] : ~ m1_subset_1(A_594,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2652])).

tff(c_2668,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_2658])).

tff(c_2669,plain,(
    ! [B_584,A_587] :
      ( r2_hidden(B_584,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_587,B_584),'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_2618])).

tff(c_3507,plain,(
    ! [B_728,D_726] :
      ( r2_hidden('#skF_4'('#skF_9',B_728,k10_relat_1('#skF_9',B_728),D_726),'#skF_8')
      | ~ r2_hidden(D_726,k10_relat_1('#skF_9',B_728))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3489,c_2669])).

tff(c_3946,plain,(
    ! [B_770,D_771] :
      ( r2_hidden('#skF_4'('#skF_9',B_770,k10_relat_1('#skF_9',B_770),D_771),'#skF_8')
      | ~ r2_hidden(D_771,k10_relat_1('#skF_9',B_770)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3507])).

tff(c_3956,plain,(
    ! [B_770,D_771] :
      ( m1_subset_1('#skF_4'('#skF_9',B_770,k10_relat_1('#skF_9',B_770),D_771),'#skF_8')
      | ~ r2_hidden(D_771,k10_relat_1('#skF_9',B_770)) ) ),
    inference(resolution,[status(thm)],[c_3946,c_32])).

tff(c_62,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2545,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2001,c_62])).

tff(c_3511,plain,(
    ! [B_728] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_728,k10_relat_1('#skF_9',B_728),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_728,k10_relat_1('#skF_9',B_728),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_728))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3489,c_2545])).

tff(c_4566,plain,(
    ! [B_837] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_837,k10_relat_1('#skF_9',B_837),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_837,k10_relat_1('#skF_9',B_837),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_837)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3511])).

tff(c_4570,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k10_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_4566])).

tff(c_4576,plain,(
    ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k10_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2589,c_4570])).

tff(c_4582,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_3956,c_4576])).

tff(c_4586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2589,c_4582])).

tff(c_4587,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6488,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6478,c_4587])).

tff(c_4603,plain,(
    ! [C_838,A_839,B_840] :
      ( v1_relat_1(C_838)
      | ~ m1_subset_1(C_838,k1_zfmisc_1(k2_zfmisc_1(A_839,B_840))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_4611,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_4603])).

tff(c_7244,plain,(
    ! [D_1275,A_1276,B_1277] :
      ( r2_hidden(k4_tarski(D_1275,'#skF_4'(A_1276,B_1277,k10_relat_1(A_1276,B_1277),D_1275)),A_1276)
      | ~ r2_hidden(D_1275,k10_relat_1(A_1276,B_1277))
      | ~ v1_relat_1(A_1276) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4625,plain,(
    ! [A_851,C_852,B_853] :
      ( m1_subset_1(A_851,C_852)
      | ~ m1_subset_1(B_853,k1_zfmisc_1(C_852))
      | ~ r2_hidden(A_851,B_853) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4631,plain,(
    ! [A_851] :
      ( m1_subset_1(A_851,k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(A_851,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_42,c_4625])).

tff(c_4620,plain,(
    ! [B_847,D_848,A_849,C_850] :
      ( r2_hidden(B_847,D_848)
      | ~ r2_hidden(k4_tarski(A_849,B_847),k2_zfmisc_1(C_850,D_848)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6509,plain,(
    ! [B_1139,D_1140,C_1141,A_1142] :
      ( r2_hidden(B_1139,D_1140)
      | v1_xboole_0(k2_zfmisc_1(C_1141,D_1140))
      | ~ m1_subset_1(k4_tarski(A_1142,B_1139),k2_zfmisc_1(C_1141,D_1140)) ) ),
    inference(resolution,[status(thm)],[c_34,c_4620])).

tff(c_6518,plain,(
    ! [B_1139,A_1142] :
      ( r2_hidden(B_1139,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(A_1142,B_1139),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4631,c_6509])).

tff(c_6519,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_6518])).

tff(c_4662,plain,(
    ! [A_860,B_861,C_862,D_863] :
      ( r2_hidden(k4_tarski(A_860,B_861),k2_zfmisc_1(C_862,D_863))
      | ~ r2_hidden(B_861,D_863)
      | ~ r2_hidden(A_860,C_862) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4678,plain,(
    ! [C_862,D_863,B_861,A_860] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_862,D_863))
      | ~ r2_hidden(B_861,D_863)
      | ~ r2_hidden(A_860,C_862) ) ),
    inference(resolution,[status(thm)],[c_4662,c_38])).

tff(c_6532,plain,(
    ! [B_861,A_860] :
      ( ~ r2_hidden(B_861,'#skF_8')
      | ~ r2_hidden(A_860,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6519,c_4678])).

tff(c_6534,plain,(
    ! [A_1147] : ~ r2_hidden(A_1147,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6532])).

tff(c_6538,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_6534])).

tff(c_6541,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_6538])).

tff(c_6545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6541,c_40])).

tff(c_6547,plain,(
    ! [B_1148] : ~ r2_hidden(B_1148,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_6532])).

tff(c_6551,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_58,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_6547])).

tff(c_6554,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_6551])).

tff(c_4689,plain,(
    ! [A_874,B_875,C_876,D_877] :
      ( k8_relset_1(A_874,B_875,C_876,D_877) = k10_relat_1(C_876,D_877)
      | ~ m1_subset_1(C_876,k1_zfmisc_1(k2_zfmisc_1(A_874,B_875))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4699,plain,(
    ! [D_877] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_877) = k10_relat_1('#skF_9',D_877) ),
    inference(resolution,[status(thm)],[c_42,c_4689])).

tff(c_4703,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4699,c_4587])).

tff(c_5623,plain,(
    ! [D_1025,A_1026,B_1027] :
      ( r2_hidden(k4_tarski(D_1025,'#skF_4'(A_1026,B_1027,k10_relat_1(A_1026,B_1027),D_1025)),A_1026)
      | ~ r2_hidden(D_1025,k10_relat_1(A_1026,B_1027))
      | ~ v1_relat_1(A_1026) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4723,plain,(
    ! [B_879,D_880,C_881,A_882] :
      ( r2_hidden(B_879,D_880)
      | v1_xboole_0(k2_zfmisc_1(C_881,D_880))
      | ~ m1_subset_1(k4_tarski(A_882,B_879),k2_zfmisc_1(C_881,D_880)) ) ),
    inference(resolution,[status(thm)],[c_34,c_4620])).

tff(c_4732,plain,(
    ! [B_879,A_882] :
      ( r2_hidden(B_879,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(A_882,B_879),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4631,c_4723])).

tff(c_4733,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_4732])).

tff(c_4736,plain,(
    ! [B_861,A_860] :
      ( ~ r2_hidden(B_861,'#skF_8')
      | ~ r2_hidden(A_860,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4733,c_4678])).

tff(c_4748,plain,(
    ! [A_887] : ~ r2_hidden(A_887,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4736])).

tff(c_4752,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_4748])).

tff(c_4755,plain,(
    ! [A_58] : ~ m1_subset_1(A_58,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4752])).

tff(c_4757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4755,c_40])).

tff(c_4759,plain,(
    ! [B_888] : ~ r2_hidden(B_888,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_4736])).

tff(c_4763,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_58,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_4759])).

tff(c_4767,plain,(
    ! [A_889] : ~ m1_subset_1(A_889,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_4763])).

tff(c_4777,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_4767])).

tff(c_4778,plain,(
    ! [B_879,A_882] :
      ( r2_hidden(B_879,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_882,B_879),'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_4732])).

tff(c_5653,plain,(
    ! [B_1027,D_1025] :
      ( r2_hidden('#skF_4'('#skF_9',B_1027,k10_relat_1('#skF_9',B_1027),D_1025),'#skF_8')
      | ~ r2_hidden(D_1025,k10_relat_1('#skF_9',B_1027))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5623,c_4778])).

tff(c_6386,plain,(
    ! [B_1112,D_1113] :
      ( r2_hidden('#skF_4'('#skF_9',B_1112,k10_relat_1('#skF_9',B_1112),D_1113),'#skF_8')
      | ~ r2_hidden(D_1113,k10_relat_1('#skF_9',B_1112)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4611,c_5653])).

tff(c_6452,plain,(
    ! [B_1122,D_1123] :
      ( m1_subset_1('#skF_4'('#skF_9',B_1122,k10_relat_1('#skF_9',B_1122),D_1123),'#skF_8')
      | ~ r2_hidden(D_1123,k10_relat_1('#skF_9',B_1122)) ) ),
    inference(resolution,[status(thm)],[c_6386,c_32])).

tff(c_4679,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_5657,plain,(
    ! [B_1027] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_1027,k10_relat_1('#skF_9',B_1027),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_1027,k10_relat_1('#skF_9',B_1027),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1027))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5623,c_4679])).

tff(c_5792,plain,(
    ! [B_1033] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_1033,k10_relat_1('#skF_9',B_1033),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_1033,k10_relat_1('#skF_9',B_1033),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1033)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4611,c_5657])).

tff(c_5796,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k10_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_5792])).

tff(c_5802,plain,(
    ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k10_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4611,c_4703,c_5796])).

tff(c_6457,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_6452,c_5802])).

tff(c_6464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4703,c_6457])).

tff(c_6465,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6554,c_6465])).

tff(c_6557,plain,(
    ! [B_1139,A_1142] :
      ( r2_hidden(B_1139,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_1142,B_1139),'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_6518])).

tff(c_7274,plain,(
    ! [B_1277,D_1275] :
      ( r2_hidden('#skF_4'('#skF_9',B_1277,k10_relat_1('#skF_9',B_1277),D_1275),'#skF_8')
      | ~ r2_hidden(D_1275,k10_relat_1('#skF_9',B_1277))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_7244,c_6557])).

tff(c_8108,plain,(
    ! [B_1367,D_1368] :
      ( r2_hidden('#skF_4'('#skF_9',B_1367,k10_relat_1('#skF_9',B_1367),D_1368),'#skF_8')
      | ~ r2_hidden(D_1368,k10_relat_1('#skF_9',B_1367)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4611,c_7274])).

tff(c_8140,plain,(
    ! [B_1377,D_1378] :
      ( m1_subset_1('#skF_4'('#skF_9',B_1377,k10_relat_1('#skF_9',B_1377),D_1378),'#skF_8')
      | ~ r2_hidden(D_1378,k10_relat_1('#skF_9',B_1377)) ) ),
    inference(resolution,[status(thm)],[c_8108,c_32])).

tff(c_4588,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6480,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4588,c_54])).

tff(c_7278,plain,(
    ! [B_1277] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_1277,k10_relat_1('#skF_9',B_1277),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_1277,k10_relat_1('#skF_9',B_1277),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1277))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_7244,c_6480])).

tff(c_7534,plain,(
    ! [B_1292] :
      ( ~ r2_hidden('#skF_4'('#skF_9',B_1292,k10_relat_1('#skF_9',B_1292),'#skF_10'),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_1292,k10_relat_1('#skF_9',B_1292),'#skF_10'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1292)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4611,c_7278])).

tff(c_7538,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k10_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_7534])).

tff(c_7544,plain,(
    ~ m1_subset_1('#skF_4'('#skF_9','#skF_7',k10_relat_1('#skF_9','#skF_7'),'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4611,c_6488,c_7538])).

tff(c_8143,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_8140,c_7544])).

tff(c_8147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_8143])).

%------------------------------------------------------------------------------
