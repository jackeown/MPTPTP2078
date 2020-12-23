%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:35 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 294 expanded)
%              Number of leaves         :   36 ( 113 expanded)
%              Depth                    :    9
%              Number of atoms          :  270 ( 880 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_109,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(D,k6_relat_1(C)))
      <=> ( r2_hidden(B,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1015,plain,(
    ! [C_350,B_351,A_352] :
      ( v5_relat_1(C_350,B_351)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_352,B_351))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1019,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_1015])).

tff(c_62,plain,(
    ! [C_121,A_122,B_123] :
      ( v1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_66,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_62])).

tff(c_1308,plain,(
    ! [A_426,B_427,C_428,D_429] :
      ( k8_relset_1(A_426,B_427,C_428,D_429) = k10_relat_1(C_428,D_429)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_426,B_427))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1311,plain,(
    ! [D_429] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_429) = k10_relat_1('#skF_5',D_429) ),
    inference(resolution,[status(thm)],[c_38,c_1308])).

tff(c_79,plain,(
    ! [C_131,B_132,A_133] :
      ( v5_relat_1(C_131,B_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_83,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_784,plain,(
    ! [A_304,B_305,C_306,D_307] :
      ( k8_relset_1(A_304,B_305,C_306,D_307) = k10_relat_1(C_306,D_307)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1(A_304,B_305))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_787,plain,(
    ! [D_307] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_307) = k10_relat_1('#skF_5',D_307) ),
    inference(resolution,[status(thm)],[c_38,c_784])).

tff(c_461,plain,(
    ! [A_233,B_234,C_235,D_236] :
      ( k8_relset_1(A_233,B_234,C_235,D_236) = k10_relat_1(C_235,D_236)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_464,plain,(
    ! [D_236] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_236) = k10_relat_1('#skF_5',D_236) ),
    inference(resolution,[status(thm)],[c_38,c_461])).

tff(c_60,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_68,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_52,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_84,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_89,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_145,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k8_relset_1(A_154,B_155,C_156,D_157) = k10_relat_1(C_156,D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_148,plain,(
    ! [D_157] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_157) = k10_relat_1('#skF_5',D_157) ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_46,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_118),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4')
      | ~ r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_288,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_118),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_46])).

tff(c_289,plain,(
    ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_108,plain,(
    ! [B_138,C_139,A_140] :
      ( r2_hidden(B_138,k2_relat_1(C_139))
      | ~ r2_hidden(k4_tarski(A_140,B_138),C_139)
      | ~ v1_relat_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_111,plain,
    ( r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_89,c_108])).

tff(c_114,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_111])).

tff(c_307,plain,(
    ! [A_199,C_200,B_201,D_202] :
      ( r2_hidden(A_199,k10_relat_1(C_200,B_201))
      | ~ r2_hidden(D_202,B_201)
      | ~ r2_hidden(k4_tarski(A_199,D_202),C_200)
      | ~ r2_hidden(D_202,k2_relat_1(C_200))
      | ~ v1_relat_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_338,plain,(
    ! [A_203,C_204] :
      ( r2_hidden(A_203,k10_relat_1(C_204,'#skF_3'))
      | ~ r2_hidden(k4_tarski(A_203,'#skF_7'),C_204)
      | ~ r2_hidden('#skF_7',k2_relat_1(C_204))
      | ~ v1_relat_1(C_204) ) ),
    inference(resolution,[status(thm)],[c_84,c_307])).

tff(c_345,plain,
    ( r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_89,c_338])).

tff(c_349,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_114,c_345])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_349])).

tff(c_403,plain,(
    ! [F_209] :
      ( ~ r2_hidden(F_209,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_209),'#skF_5')
      | ~ m1_subset_1(F_209,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_410,plain,
    ( ~ r2_hidden('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_89,c_403])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_84,c_410])).

tff(c_418,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_466,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_418])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden(k4_tarski(A_5,'#skF_1'(A_5,B_6,C_7)),C_7)
      | ~ r2_hidden(A_5,k10_relat_1(C_7,B_6))
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_424,plain,(
    ! [B_210,A_211] :
      ( k5_relat_1(B_210,k6_relat_1(A_211)) = B_210
      | ~ r1_tarski(k2_relat_1(B_210),A_211)
      | ~ v1_relat_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_428,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_424])).

tff(c_445,plain,(
    ! [B_223,C_224,A_225,D_226] :
      ( r2_hidden(B_223,C_224)
      | ~ r2_hidden(k4_tarski(A_225,B_223),k5_relat_1(D_226,k6_relat_1(C_224)))
      | ~ v1_relat_1(D_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_592,plain,(
    ! [B_259,A_260,A_261,B_262] :
      ( r2_hidden(B_259,A_260)
      | ~ r2_hidden(k4_tarski(A_261,B_259),B_262)
      | ~ v1_relat_1(B_262)
      | ~ v5_relat_1(B_262,A_260)
      | ~ v1_relat_1(B_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_445])).

tff(c_599,plain,(
    ! [A_263,B_264,C_265,A_266] :
      ( r2_hidden('#skF_1'(A_263,B_264,C_265),A_266)
      | ~ v5_relat_1(C_265,A_266)
      | ~ r2_hidden(A_263,k10_relat_1(C_265,B_264))
      | ~ v1_relat_1(C_265) ) ),
    inference(resolution,[status(thm)],[c_12,c_592])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_615,plain,(
    ! [A_267,B_268,C_269,A_270] :
      ( m1_subset_1('#skF_1'(A_267,B_268,C_269),A_270)
      | ~ v5_relat_1(C_269,A_270)
      | ~ r2_hidden(A_267,k10_relat_1(C_269,B_268))
      | ~ v1_relat_1(C_269) ) ),
    inference(resolution,[status(thm)],[c_599,c_2])).

tff(c_620,plain,(
    ! [A_270] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_270)
      | ~ v5_relat_1('#skF_5',A_270)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_466,c_615])).

tff(c_630,plain,(
    ! [A_270] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_270)
      | ~ v5_relat_1('#skF_5',A_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_620])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_7),B_6)
      | ~ r2_hidden(A_5,k10_relat_1(C_7,B_6))
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_419,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_118),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4')
      | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_509,plain,(
    ! [F_241] :
      ( ~ r2_hidden(F_241,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_241),'#skF_5')
      | ~ m1_subset_1(F_241,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_54])).

tff(c_513,plain,(
    ! [B_6] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_6,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_6,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_6))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_509])).

tff(c_686,plain,(
    ! [B_280] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_280,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_280,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_280)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_513])).

tff(c_694,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_686])).

tff(c_700,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_466,c_694])).

tff(c_740,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_630,c_700])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_740])).

tff(c_745,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_794,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_745])).

tff(c_753,plain,(
    ! [B_289,A_290] :
      ( k5_relat_1(B_289,k6_relat_1(A_290)) = B_289
      | ~ r1_tarski(k2_relat_1(B_289),A_290)
      | ~ v1_relat_1(B_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_757,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_753])).

tff(c_768,plain,(
    ! [B_293,C_294,A_295,D_296] :
      ( r2_hidden(B_293,C_294)
      | ~ r2_hidden(k4_tarski(A_295,B_293),k5_relat_1(D_296,k6_relat_1(C_294)))
      | ~ v1_relat_1(D_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_897,plain,(
    ! [B_328,A_329,A_330,B_331] :
      ( r2_hidden(B_328,A_329)
      | ~ r2_hidden(k4_tarski(A_330,B_328),B_331)
      | ~ v1_relat_1(B_331)
      | ~ v5_relat_1(B_331,A_329)
      | ~ v1_relat_1(B_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_768])).

tff(c_901,plain,(
    ! [A_332,B_333,C_334,A_335] :
      ( r2_hidden('#skF_1'(A_332,B_333,C_334),A_335)
      | ~ v5_relat_1(C_334,A_335)
      | ~ r2_hidden(A_332,k10_relat_1(C_334,B_333))
      | ~ v1_relat_1(C_334) ) ),
    inference(resolution,[status(thm)],[c_12,c_897])).

tff(c_915,plain,(
    ! [A_336,B_337,C_338,A_339] :
      ( m1_subset_1('#skF_1'(A_336,B_337,C_338),A_339)
      | ~ v5_relat_1(C_338,A_339)
      | ~ r2_hidden(A_336,k10_relat_1(C_338,B_337))
      | ~ v1_relat_1(C_338) ) ),
    inference(resolution,[status(thm)],[c_901,c_2])).

tff(c_923,plain,(
    ! [A_339] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_339)
      | ~ v5_relat_1('#skF_5',A_339)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_794,c_915])).

tff(c_931,plain,(
    ! [A_339] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_339)
      | ~ v5_relat_1('#skF_5',A_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_923])).

tff(c_820,plain,(
    ! [A_319,B_320,C_321] :
      ( r2_hidden(k4_tarski(A_319,'#skF_1'(A_319,B_320,C_321)),C_321)
      | ~ r2_hidden(A_319,k10_relat_1(C_321,B_320))
      | ~ v1_relat_1(C_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_746,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_118),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4')
      | r2_hidden('#skF_7','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_782,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_118),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_746,c_50])).

tff(c_828,plain,(
    ! [B_320] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_320,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_320,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_320))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_820,c_782])).

tff(c_982,plain,(
    ! [B_347] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_347,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_347,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_347)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_828])).

tff(c_990,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_982])).

tff(c_996,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_794,c_990])).

tff(c_999,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_931,c_996])).

tff(c_1003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_999])).

tff(c_1004,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1313,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1311,c_1004])).

tff(c_1028,plain,(
    ! [B_362,A_363] :
      ( k5_relat_1(B_362,k6_relat_1(A_363)) = B_362
      | ~ r1_tarski(k2_relat_1(B_362),A_363)
      | ~ v1_relat_1(B_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1032,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_1028])).

tff(c_1048,plain,(
    ! [B_369,C_370,A_371,D_372] :
      ( r2_hidden(B_369,C_370)
      | ~ r2_hidden(k4_tarski(A_371,B_369),k5_relat_1(D_372,k6_relat_1(C_370)))
      | ~ v1_relat_1(D_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1413,plain,(
    ! [B_447,A_448,A_449,B_450] :
      ( r2_hidden(B_447,A_448)
      | ~ r2_hidden(k4_tarski(A_449,B_447),B_450)
      | ~ v1_relat_1(B_450)
      | ~ v5_relat_1(B_450,A_448)
      | ~ v1_relat_1(B_450) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_1048])).

tff(c_1419,plain,(
    ! [A_451,B_452,C_453,A_454] :
      ( r2_hidden('#skF_1'(A_451,B_452,C_453),A_454)
      | ~ v5_relat_1(C_453,A_454)
      | ~ r2_hidden(A_451,k10_relat_1(C_453,B_452))
      | ~ v1_relat_1(C_453) ) ),
    inference(resolution,[status(thm)],[c_12,c_1413])).

tff(c_1433,plain,(
    ! [A_455,B_456,C_457,A_458] :
      ( m1_subset_1('#skF_1'(A_455,B_456,C_457),A_458)
      | ~ v5_relat_1(C_457,A_458)
      | ~ r2_hidden(A_455,k10_relat_1(C_457,B_456))
      | ~ v1_relat_1(C_457) ) ),
    inference(resolution,[status(thm)],[c_1419,c_2])).

tff(c_1441,plain,(
    ! [A_458] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_458)
      | ~ v5_relat_1('#skF_5',A_458)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1313,c_1433])).

tff(c_1449,plain,(
    ! [A_458] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_458)
      | ~ v5_relat_1('#skF_5',A_458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1441])).

tff(c_1333,plain,(
    ! [A_431,B_432,C_433] :
      ( r2_hidden(k4_tarski(A_431,'#skF_1'(A_431,B_432,C_433)),C_433)
      | ~ r2_hidden(A_431,k10_relat_1(C_433,B_432))
      | ~ v1_relat_1(C_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1005,plain,(
    ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_118),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4')
      | m1_subset_1('#skF_7','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1306,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_118),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1005,c_58])).

tff(c_1337,plain,(
    ! [B_432] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_432,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_432,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_432))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1333,c_1306])).

tff(c_1471,plain,(
    ! [B_460] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_460,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_460,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_460)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1337])).

tff(c_1479,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1471])).

tff(c_1485,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1313,c_1479])).

tff(c_1488,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1449,c_1485])).

tff(c_1492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1019,c_1488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:15:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.65  
% 3.93/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.65  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.93/1.65  
% 3.93/1.65  %Foreground sorts:
% 3.93/1.65  
% 3.93/1.65  
% 3.93/1.65  %Background operators:
% 3.93/1.65  
% 3.93/1.65  
% 3.93/1.65  %Foreground operators:
% 3.93/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.93/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.93/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.93/1.65  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.93/1.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.93/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.93/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.93/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.93/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.93/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.93/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.93/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.93/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.93/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.65  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.93/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.93/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.93/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.93/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.93/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.93/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.93/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.93/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.93/1.65  
% 4.14/1.68  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 4.14/1.68  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.14/1.68  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.14/1.68  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.14/1.68  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 4.14/1.68  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 4.14/1.68  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.14/1.68  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 4.14/1.68  tff(f_62, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(D, k6_relat_1(C))) <=> (r2_hidden(B, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_relat_1)).
% 4.14/1.68  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.14/1.68  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.14/1.68  tff(c_1015, plain, (![C_350, B_351, A_352]: (v5_relat_1(C_350, B_351) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_352, B_351))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.14/1.68  tff(c_1019, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_1015])).
% 4.14/1.68  tff(c_62, plain, (![C_121, A_122, B_123]: (v1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.14/1.68  tff(c_66, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_62])).
% 4.14/1.68  tff(c_1308, plain, (![A_426, B_427, C_428, D_429]: (k8_relset_1(A_426, B_427, C_428, D_429)=k10_relat_1(C_428, D_429) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_426, B_427))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.14/1.68  tff(c_1311, plain, (![D_429]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_429)=k10_relat_1('#skF_5', D_429))), inference(resolution, [status(thm)], [c_38, c_1308])).
% 4.14/1.68  tff(c_79, plain, (![C_131, B_132, A_133]: (v5_relat_1(C_131, B_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.14/1.68  tff(c_83, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_79])).
% 4.14/1.68  tff(c_784, plain, (![A_304, B_305, C_306, D_307]: (k8_relset_1(A_304, B_305, C_306, D_307)=k10_relat_1(C_306, D_307) | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1(A_304, B_305))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.14/1.68  tff(c_787, plain, (![D_307]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_307)=k10_relat_1('#skF_5', D_307))), inference(resolution, [status(thm)], [c_38, c_784])).
% 4.14/1.68  tff(c_461, plain, (![A_233, B_234, C_235, D_236]: (k8_relset_1(A_233, B_234, C_235, D_236)=k10_relat_1(C_235, D_236) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.14/1.68  tff(c_464, plain, (![D_236]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_236)=k10_relat_1('#skF_5', D_236))), inference(resolution, [status(thm)], [c_38, c_461])).
% 4.14/1.68  tff(c_60, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.14/1.68  tff(c_68, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 4.14/1.68  tff(c_52, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.14/1.68  tff(c_84, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 4.14/1.68  tff(c_56, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.14/1.68  tff(c_89, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 4.14/1.68  tff(c_145, plain, (![A_154, B_155, C_156, D_157]: (k8_relset_1(A_154, B_155, C_156, D_157)=k10_relat_1(C_156, D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.14/1.68  tff(c_148, plain, (![D_157]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_157)=k10_relat_1('#skF_5', D_157))), inference(resolution, [status(thm)], [c_38, c_145])).
% 4.14/1.68  tff(c_46, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_118), '#skF_5') | ~m1_subset_1(F_118, '#skF_4') | ~r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.14/1.68  tff(c_288, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_118), '#skF_5') | ~m1_subset_1(F_118, '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_46])).
% 4.14/1.68  tff(c_289, plain, (~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_288])).
% 4.14/1.68  tff(c_108, plain, (![B_138, C_139, A_140]: (r2_hidden(B_138, k2_relat_1(C_139)) | ~r2_hidden(k4_tarski(A_140, B_138), C_139) | ~v1_relat_1(C_139))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.14/1.68  tff(c_111, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_89, c_108])).
% 4.14/1.68  tff(c_114, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_111])).
% 4.14/1.68  tff(c_307, plain, (![A_199, C_200, B_201, D_202]: (r2_hidden(A_199, k10_relat_1(C_200, B_201)) | ~r2_hidden(D_202, B_201) | ~r2_hidden(k4_tarski(A_199, D_202), C_200) | ~r2_hidden(D_202, k2_relat_1(C_200)) | ~v1_relat_1(C_200))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.14/1.68  tff(c_338, plain, (![A_203, C_204]: (r2_hidden(A_203, k10_relat_1(C_204, '#skF_3')) | ~r2_hidden(k4_tarski(A_203, '#skF_7'), C_204) | ~r2_hidden('#skF_7', k2_relat_1(C_204)) | ~v1_relat_1(C_204))), inference(resolution, [status(thm)], [c_84, c_307])).
% 4.14/1.68  tff(c_345, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_89, c_338])).
% 4.14/1.68  tff(c_349, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_114, c_345])).
% 4.14/1.68  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_289, c_349])).
% 4.14/1.68  tff(c_403, plain, (![F_209]: (~r2_hidden(F_209, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_209), '#skF_5') | ~m1_subset_1(F_209, '#skF_4'))), inference(splitRight, [status(thm)], [c_288])).
% 4.14/1.68  tff(c_410, plain, (~r2_hidden('#skF_7', '#skF_3') | ~m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_89, c_403])).
% 4.14/1.68  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_84, c_410])).
% 4.14/1.68  tff(c_418, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_56])).
% 4.14/1.68  tff(c_466, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_418])).
% 4.14/1.68  tff(c_12, plain, (![A_5, B_6, C_7]: (r2_hidden(k4_tarski(A_5, '#skF_1'(A_5, B_6, C_7)), C_7) | ~r2_hidden(A_5, k10_relat_1(C_7, B_6)) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.14/1.68  tff(c_6, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.14/1.68  tff(c_424, plain, (![B_210, A_211]: (k5_relat_1(B_210, k6_relat_1(A_211))=B_210 | ~r1_tarski(k2_relat_1(B_210), A_211) | ~v1_relat_1(B_210))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.14/1.68  tff(c_428, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_6, c_424])).
% 4.14/1.68  tff(c_445, plain, (![B_223, C_224, A_225, D_226]: (r2_hidden(B_223, C_224) | ~r2_hidden(k4_tarski(A_225, B_223), k5_relat_1(D_226, k6_relat_1(C_224))) | ~v1_relat_1(D_226))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.14/1.68  tff(c_592, plain, (![B_259, A_260, A_261, B_262]: (r2_hidden(B_259, A_260) | ~r2_hidden(k4_tarski(A_261, B_259), B_262) | ~v1_relat_1(B_262) | ~v5_relat_1(B_262, A_260) | ~v1_relat_1(B_262))), inference(superposition, [status(thm), theory('equality')], [c_428, c_445])).
% 4.14/1.68  tff(c_599, plain, (![A_263, B_264, C_265, A_266]: (r2_hidden('#skF_1'(A_263, B_264, C_265), A_266) | ~v5_relat_1(C_265, A_266) | ~r2_hidden(A_263, k10_relat_1(C_265, B_264)) | ~v1_relat_1(C_265))), inference(resolution, [status(thm)], [c_12, c_592])).
% 4.14/1.68  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.14/1.68  tff(c_615, plain, (![A_267, B_268, C_269, A_270]: (m1_subset_1('#skF_1'(A_267, B_268, C_269), A_270) | ~v5_relat_1(C_269, A_270) | ~r2_hidden(A_267, k10_relat_1(C_269, B_268)) | ~v1_relat_1(C_269))), inference(resolution, [status(thm)], [c_599, c_2])).
% 4.14/1.68  tff(c_620, plain, (![A_270]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_270) | ~v5_relat_1('#skF_5', A_270) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_466, c_615])).
% 4.14/1.68  tff(c_630, plain, (![A_270]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_270) | ~v5_relat_1('#skF_5', A_270))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_620])).
% 4.14/1.68  tff(c_10, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_1'(A_5, B_6, C_7), B_6) | ~r2_hidden(A_5, k10_relat_1(C_7, B_6)) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.14/1.68  tff(c_419, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 4.14/1.68  tff(c_54, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_118), '#skF_5') | ~m1_subset_1(F_118, '#skF_4') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.14/1.68  tff(c_509, plain, (![F_241]: (~r2_hidden(F_241, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_241), '#skF_5') | ~m1_subset_1(F_241, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_419, c_54])).
% 4.14/1.68  tff(c_513, plain, (![B_6]: (~r2_hidden('#skF_1'('#skF_6', B_6, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_6, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_6)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_509])).
% 4.14/1.68  tff(c_686, plain, (![B_280]: (~r2_hidden('#skF_1'('#skF_6', B_280, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_280, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_280)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_513])).
% 4.14/1.68  tff(c_694, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_686])).
% 4.14/1.68  tff(c_700, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_466, c_694])).
% 4.14/1.68  tff(c_740, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_630, c_700])).
% 4.14/1.68  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_740])).
% 4.14/1.68  tff(c_745, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 4.14/1.68  tff(c_794, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_745])).
% 4.14/1.68  tff(c_753, plain, (![B_289, A_290]: (k5_relat_1(B_289, k6_relat_1(A_290))=B_289 | ~r1_tarski(k2_relat_1(B_289), A_290) | ~v1_relat_1(B_289))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.14/1.68  tff(c_757, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_6, c_753])).
% 4.14/1.68  tff(c_768, plain, (![B_293, C_294, A_295, D_296]: (r2_hidden(B_293, C_294) | ~r2_hidden(k4_tarski(A_295, B_293), k5_relat_1(D_296, k6_relat_1(C_294))) | ~v1_relat_1(D_296))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.14/1.68  tff(c_897, plain, (![B_328, A_329, A_330, B_331]: (r2_hidden(B_328, A_329) | ~r2_hidden(k4_tarski(A_330, B_328), B_331) | ~v1_relat_1(B_331) | ~v5_relat_1(B_331, A_329) | ~v1_relat_1(B_331))), inference(superposition, [status(thm), theory('equality')], [c_757, c_768])).
% 4.14/1.68  tff(c_901, plain, (![A_332, B_333, C_334, A_335]: (r2_hidden('#skF_1'(A_332, B_333, C_334), A_335) | ~v5_relat_1(C_334, A_335) | ~r2_hidden(A_332, k10_relat_1(C_334, B_333)) | ~v1_relat_1(C_334))), inference(resolution, [status(thm)], [c_12, c_897])).
% 4.14/1.68  tff(c_915, plain, (![A_336, B_337, C_338, A_339]: (m1_subset_1('#skF_1'(A_336, B_337, C_338), A_339) | ~v5_relat_1(C_338, A_339) | ~r2_hidden(A_336, k10_relat_1(C_338, B_337)) | ~v1_relat_1(C_338))), inference(resolution, [status(thm)], [c_901, c_2])).
% 4.14/1.68  tff(c_923, plain, (![A_339]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_339) | ~v5_relat_1('#skF_5', A_339) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_794, c_915])).
% 4.14/1.68  tff(c_931, plain, (![A_339]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_339) | ~v5_relat_1('#skF_5', A_339))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_923])).
% 4.14/1.68  tff(c_820, plain, (![A_319, B_320, C_321]: (r2_hidden(k4_tarski(A_319, '#skF_1'(A_319, B_320, C_321)), C_321) | ~r2_hidden(A_319, k10_relat_1(C_321, B_320)) | ~v1_relat_1(C_321))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.14/1.68  tff(c_746, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 4.14/1.68  tff(c_50, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_118), '#skF_5') | ~m1_subset_1(F_118, '#skF_4') | r2_hidden('#skF_7', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.14/1.68  tff(c_782, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_118), '#skF_5') | ~m1_subset_1(F_118, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_746, c_50])).
% 4.14/1.68  tff(c_828, plain, (![B_320]: (~r2_hidden('#skF_1'('#skF_6', B_320, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_320, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_320)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_820, c_782])).
% 4.14/1.68  tff(c_982, plain, (![B_347]: (~r2_hidden('#skF_1'('#skF_6', B_347, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_347, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_347)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_828])).
% 4.14/1.68  tff(c_990, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_982])).
% 4.14/1.68  tff(c_996, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_794, c_990])).
% 4.14/1.68  tff(c_999, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_931, c_996])).
% 4.14/1.68  tff(c_1003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_999])).
% 4.14/1.68  tff(c_1004, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 4.14/1.68  tff(c_1313, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1311, c_1004])).
% 4.14/1.68  tff(c_1028, plain, (![B_362, A_363]: (k5_relat_1(B_362, k6_relat_1(A_363))=B_362 | ~r1_tarski(k2_relat_1(B_362), A_363) | ~v1_relat_1(B_362))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.14/1.68  tff(c_1032, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_6, c_1028])).
% 4.14/1.68  tff(c_1048, plain, (![B_369, C_370, A_371, D_372]: (r2_hidden(B_369, C_370) | ~r2_hidden(k4_tarski(A_371, B_369), k5_relat_1(D_372, k6_relat_1(C_370))) | ~v1_relat_1(D_372))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.14/1.68  tff(c_1413, plain, (![B_447, A_448, A_449, B_450]: (r2_hidden(B_447, A_448) | ~r2_hidden(k4_tarski(A_449, B_447), B_450) | ~v1_relat_1(B_450) | ~v5_relat_1(B_450, A_448) | ~v1_relat_1(B_450))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_1048])).
% 4.14/1.68  tff(c_1419, plain, (![A_451, B_452, C_453, A_454]: (r2_hidden('#skF_1'(A_451, B_452, C_453), A_454) | ~v5_relat_1(C_453, A_454) | ~r2_hidden(A_451, k10_relat_1(C_453, B_452)) | ~v1_relat_1(C_453))), inference(resolution, [status(thm)], [c_12, c_1413])).
% 4.14/1.68  tff(c_1433, plain, (![A_455, B_456, C_457, A_458]: (m1_subset_1('#skF_1'(A_455, B_456, C_457), A_458) | ~v5_relat_1(C_457, A_458) | ~r2_hidden(A_455, k10_relat_1(C_457, B_456)) | ~v1_relat_1(C_457))), inference(resolution, [status(thm)], [c_1419, c_2])).
% 4.14/1.68  tff(c_1441, plain, (![A_458]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_458) | ~v5_relat_1('#skF_5', A_458) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1313, c_1433])).
% 4.14/1.68  tff(c_1449, plain, (![A_458]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_458) | ~v5_relat_1('#skF_5', A_458))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1441])).
% 4.14/1.68  tff(c_1333, plain, (![A_431, B_432, C_433]: (r2_hidden(k4_tarski(A_431, '#skF_1'(A_431, B_432, C_433)), C_433) | ~r2_hidden(A_431, k10_relat_1(C_433, B_432)) | ~v1_relat_1(C_433))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.14/1.68  tff(c_1005, plain, (~m1_subset_1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 4.14/1.68  tff(c_58, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_118), '#skF_5') | ~m1_subset_1(F_118, '#skF_4') | m1_subset_1('#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.14/1.68  tff(c_1306, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_118), '#skF_5') | ~m1_subset_1(F_118, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1005, c_58])).
% 4.14/1.68  tff(c_1337, plain, (![B_432]: (~r2_hidden('#skF_1'('#skF_6', B_432, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_432, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_432)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1333, c_1306])).
% 4.14/1.68  tff(c_1471, plain, (![B_460]: (~r2_hidden('#skF_1'('#skF_6', B_460, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_460, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_460)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1337])).
% 4.14/1.68  tff(c_1479, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_1471])).
% 4.14/1.68  tff(c_1485, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1313, c_1479])).
% 4.14/1.68  tff(c_1488, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1449, c_1485])).
% 4.14/1.68  tff(c_1492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1019, c_1488])).
% 4.14/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.68  
% 4.14/1.68  Inference rules
% 4.14/1.68  ----------------------
% 4.14/1.68  #Ref     : 0
% 4.14/1.68  #Sup     : 297
% 4.14/1.68  #Fact    : 0
% 4.14/1.68  #Define  : 0
% 4.14/1.68  #Split   : 8
% 4.14/1.68  #Chain   : 0
% 4.14/1.68  #Close   : 0
% 4.14/1.68  
% 4.14/1.68  Ordering : KBO
% 4.14/1.68  
% 4.14/1.68  Simplification rules
% 4.14/1.68  ----------------------
% 4.14/1.68  #Subsume      : 22
% 4.14/1.68  #Demod        : 74
% 4.14/1.68  #Tautology    : 52
% 4.14/1.68  #SimpNegUnit  : 5
% 4.14/1.68  #BackRed      : 8
% 4.14/1.68  
% 4.14/1.68  #Partial instantiations: 0
% 4.14/1.68  #Strategies tried      : 1
% 4.14/1.68  
% 4.14/1.68  Timing (in seconds)
% 4.14/1.68  ----------------------
% 4.14/1.68  Preprocessing        : 0.34
% 4.14/1.68  Parsing              : 0.18
% 4.14/1.68  CNF conversion       : 0.03
% 4.14/1.68  Main loop            : 0.54
% 4.14/1.68  Inferencing          : 0.22
% 4.14/1.68  Reduction            : 0.15
% 4.14/1.68  Demodulation         : 0.10
% 4.14/1.68  BG Simplification    : 0.03
% 4.14/1.68  Subsumption          : 0.10
% 4.14/1.68  Abstraction          : 0.03
% 4.14/1.68  MUC search           : 0.00
% 4.14/1.69  Cooper               : 0.00
% 4.14/1.69  Total                : 0.94
% 4.14/1.69  Index Insertion      : 0.00
% 4.14/1.69  Index Deletion       : 0.00
% 4.14/1.69  Index Matching       : 0.00
% 4.14/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
