%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:32 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.76s
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
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(F,E),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

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
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1020,plain,(
    ! [C_353,A_354,B_355] :
      ( v4_relat_1(C_353,A_354)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_354,B_355))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1024,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_1020])).

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
      ( k7_relset_1(A_426,B_427,C_428,D_429) = k9_relat_1(C_428,D_429)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_426,B_427))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1311,plain,(
    ! [D_429] : k7_relset_1('#skF_4','#skF_2','#skF_5',D_429) = k9_relat_1('#skF_5',D_429) ),
    inference(resolution,[status(thm)],[c_38,c_1308])).

tff(c_74,plain,(
    ! [C_128,A_129,B_130] :
      ( v4_relat_1(C_128,A_129)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_784,plain,(
    ! [A_304,B_305,C_306,D_307] :
      ( k7_relset_1(A_304,B_305,C_306,D_307) = k9_relat_1(C_306,D_307)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1(A_304,B_305))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_787,plain,(
    ! [D_307] : k7_relset_1('#skF_4','#skF_2','#skF_5',D_307) = k9_relat_1('#skF_5',D_307) ),
    inference(resolution,[status(thm)],[c_38,c_784])).

tff(c_461,plain,(
    ! [A_233,B_234,C_235,D_236] :
      ( k7_relset_1(A_233,B_234,C_235,D_236) = k9_relat_1(C_235,D_236)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_464,plain,(
    ! [D_236] : k7_relset_1('#skF_4','#skF_2','#skF_5',D_236) = k9_relat_1('#skF_5',D_236) ),
    inference(resolution,[status(thm)],[c_38,c_461])).

tff(c_60,plain,
    ( r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_68,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_52,plain,
    ( r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | r2_hidden('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_84,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,
    ( r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_89,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_145,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k7_relset_1(A_154,B_155,C_156,D_157) = k9_relat_1(C_156,D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_148,plain,(
    ! [D_157] : k7_relset_1('#skF_4','#skF_2','#skF_5',D_157) = k9_relat_1('#skF_5',D_157) ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_46,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_118,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4')
      | ~ r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_288,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_118,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_46])).

tff(c_289,plain,(
    ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_115,plain,(
    ! [A_141,C_142,B_143] :
      ( r2_hidden(A_141,k1_relat_1(C_142))
      | ~ r2_hidden(k4_tarski(A_141,B_143),C_142)
      | ~ v1_relat_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_118,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_89,c_115])).

tff(c_121,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_118])).

tff(c_307,plain,(
    ! [A_199,C_200,B_201,D_202] :
      ( r2_hidden(A_199,k9_relat_1(C_200,B_201))
      | ~ r2_hidden(D_202,B_201)
      | ~ r2_hidden(k4_tarski(D_202,A_199),C_200)
      | ~ r2_hidden(D_202,k1_relat_1(C_200))
      | ~ v1_relat_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_338,plain,(
    ! [A_203,C_204] :
      ( r2_hidden(A_203,k9_relat_1(C_204,'#skF_3'))
      | ~ r2_hidden(k4_tarski('#skF_7',A_203),C_204)
      | ~ r2_hidden('#skF_7',k1_relat_1(C_204))
      | ~ v1_relat_1(C_204) ) ),
    inference(resolution,[status(thm)],[c_84,c_307])).

tff(c_345,plain,
    ( r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_89,c_338])).

tff(c_349,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_121,c_345])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_349])).

tff(c_403,plain,(
    ! [F_209] :
      ( ~ r2_hidden(F_209,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_209,'#skF_6'),'#skF_5')
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
    r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_466,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_418])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden(k4_tarski('#skF_1'(A_5,B_6,C_7),A_5),C_7)
      | ~ r2_hidden(A_5,k9_relat_1(C_7,B_6))
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_424,plain,(
    ! [A_210,B_211] :
      ( k5_relat_1(k6_relat_1(A_210),B_211) = B_211
      | ~ r1_tarski(k1_relat_1(B_211),A_210)
      | ~ v1_relat_1(B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_428,plain,(
    ! [A_3,B_4] :
      ( k5_relat_1(k6_relat_1(A_3),B_4) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_424])).

tff(c_445,plain,(
    ! [A_223,C_224,B_225,D_226] :
      ( r2_hidden(A_223,C_224)
      | ~ r2_hidden(k4_tarski(A_223,B_225),k5_relat_1(k6_relat_1(C_224),D_226))
      | ~ v1_relat_1(D_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_592,plain,(
    ! [A_259,A_260,B_261,B_262] :
      ( r2_hidden(A_259,A_260)
      | ~ r2_hidden(k4_tarski(A_259,B_261),B_262)
      | ~ v1_relat_1(B_262)
      | ~ v4_relat_1(B_262,A_260)
      | ~ v1_relat_1(B_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_445])).

tff(c_599,plain,(
    ! [A_263,B_264,C_265,A_266] :
      ( r2_hidden('#skF_1'(A_263,B_264,C_265),A_266)
      | ~ v4_relat_1(C_265,A_266)
      | ~ r2_hidden(A_263,k9_relat_1(C_265,B_264))
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
      | ~ v4_relat_1(C_269,A_270)
      | ~ r2_hidden(A_267,k9_relat_1(C_269,B_268))
      | ~ v1_relat_1(C_269) ) ),
    inference(resolution,[status(thm)],[c_599,c_2])).

tff(c_620,plain,(
    ! [A_270] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_270)
      | ~ v4_relat_1('#skF_5',A_270)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_466,c_615])).

tff(c_630,plain,(
    ! [A_270] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_270)
      | ~ v4_relat_1('#skF_5',A_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_620])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_7),B_6)
      | ~ r2_hidden(A_5,k9_relat_1(C_7,B_6))
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_419,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_118,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4')
      | r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_509,plain,(
    ! [F_241] :
      ( ~ r2_hidden(F_241,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_241,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_241,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_54])).

tff(c_513,plain,(
    ! [B_6] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_6,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_6,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_6))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_509])).

tff(c_686,plain,(
    ! [B_280] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_280,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_280,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_280)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_513])).

tff(c_694,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_686])).

tff(c_700,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_466,c_694])).

tff(c_740,plain,(
    ~ v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_630,c_700])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_740])).

tff(c_745,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_794,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_745])).

tff(c_753,plain,(
    ! [A_289,B_290] :
      ( k5_relat_1(k6_relat_1(A_289),B_290) = B_290
      | ~ r1_tarski(k1_relat_1(B_290),A_289)
      | ~ v1_relat_1(B_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_757,plain,(
    ! [A_3,B_4] :
      ( k5_relat_1(k6_relat_1(A_3),B_4) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_753])).

tff(c_768,plain,(
    ! [A_293,C_294,B_295,D_296] :
      ( r2_hidden(A_293,C_294)
      | ~ r2_hidden(k4_tarski(A_293,B_295),k5_relat_1(k6_relat_1(C_294),D_296))
      | ~ v1_relat_1(D_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_897,plain,(
    ! [A_328,A_329,B_330,B_331] :
      ( r2_hidden(A_328,A_329)
      | ~ r2_hidden(k4_tarski(A_328,B_330),B_331)
      | ~ v1_relat_1(B_331)
      | ~ v4_relat_1(B_331,A_329)
      | ~ v1_relat_1(B_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_768])).

tff(c_901,plain,(
    ! [A_332,B_333,C_334,A_335] :
      ( r2_hidden('#skF_1'(A_332,B_333,C_334),A_335)
      | ~ v4_relat_1(C_334,A_335)
      | ~ r2_hidden(A_332,k9_relat_1(C_334,B_333))
      | ~ v1_relat_1(C_334) ) ),
    inference(resolution,[status(thm)],[c_12,c_897])).

tff(c_915,plain,(
    ! [A_336,B_337,C_338,A_339] :
      ( m1_subset_1('#skF_1'(A_336,B_337,C_338),A_339)
      | ~ v4_relat_1(C_338,A_339)
      | ~ r2_hidden(A_336,k9_relat_1(C_338,B_337))
      | ~ v1_relat_1(C_338) ) ),
    inference(resolution,[status(thm)],[c_901,c_2])).

tff(c_923,plain,(
    ! [A_339] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_339)
      | ~ v4_relat_1('#skF_5',A_339)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_794,c_915])).

tff(c_931,plain,(
    ! [A_339] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_339)
      | ~ v4_relat_1('#skF_5',A_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_923])).

tff(c_820,plain,(
    ! [A_319,B_320,C_321] :
      ( r2_hidden(k4_tarski('#skF_1'(A_319,B_320,C_321),A_319),C_321)
      | ~ r2_hidden(A_319,k9_relat_1(C_321,B_320))
      | ~ v1_relat_1(C_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_746,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_118,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4')
      | r2_hidden('#skF_7','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_782,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_118,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_746,c_50])).

tff(c_828,plain,(
    ! [B_320] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_320,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_320,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_320))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_820,c_782])).

tff(c_982,plain,(
    ! [B_347] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_347,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_347,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_347)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_828])).

tff(c_990,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_982])).

tff(c_996,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_794,c_990])).

tff(c_999,plain,(
    ~ v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_931,c_996])).

tff(c_1003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_999])).

tff(c_1004,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1313,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1311,c_1004])).

tff(c_1028,plain,(
    ! [A_362,B_363] :
      ( k5_relat_1(k6_relat_1(A_362),B_363) = B_363
      | ~ r1_tarski(k1_relat_1(B_363),A_362)
      | ~ v1_relat_1(B_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1032,plain,(
    ! [A_3,B_4] :
      ( k5_relat_1(k6_relat_1(A_3),B_4) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_1028])).

tff(c_1048,plain,(
    ! [A_369,C_370,B_371,D_372] :
      ( r2_hidden(A_369,C_370)
      | ~ r2_hidden(k4_tarski(A_369,B_371),k5_relat_1(k6_relat_1(C_370),D_372))
      | ~ v1_relat_1(D_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1413,plain,(
    ! [A_447,A_448,B_449,B_450] :
      ( r2_hidden(A_447,A_448)
      | ~ r2_hidden(k4_tarski(A_447,B_449),B_450)
      | ~ v1_relat_1(B_450)
      | ~ v4_relat_1(B_450,A_448)
      | ~ v1_relat_1(B_450) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_1048])).

tff(c_1419,plain,(
    ! [A_451,B_452,C_453,A_454] :
      ( r2_hidden('#skF_1'(A_451,B_452,C_453),A_454)
      | ~ v4_relat_1(C_453,A_454)
      | ~ r2_hidden(A_451,k9_relat_1(C_453,B_452))
      | ~ v1_relat_1(C_453) ) ),
    inference(resolution,[status(thm)],[c_12,c_1413])).

tff(c_1433,plain,(
    ! [A_455,B_456,C_457,A_458] :
      ( m1_subset_1('#skF_1'(A_455,B_456,C_457),A_458)
      | ~ v4_relat_1(C_457,A_458)
      | ~ r2_hidden(A_455,k9_relat_1(C_457,B_456))
      | ~ v1_relat_1(C_457) ) ),
    inference(resolution,[status(thm)],[c_1419,c_2])).

tff(c_1441,plain,(
    ! [A_458] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_458)
      | ~ v4_relat_1('#skF_5',A_458)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1313,c_1433])).

tff(c_1449,plain,(
    ! [A_458] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_458)
      | ~ v4_relat_1('#skF_5',A_458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1441])).

tff(c_1333,plain,(
    ! [A_431,B_432,C_433] :
      ( r2_hidden(k4_tarski('#skF_1'(A_431,B_432,C_433),A_431),C_433)
      | ~ r2_hidden(A_431,k9_relat_1(C_433,B_432))
      | ~ v1_relat_1(C_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1005,plain,(
    ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_118,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4')
      | m1_subset_1('#skF_7','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1306,plain,(
    ! [F_118] :
      ( ~ r2_hidden(F_118,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_118,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_118,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1005,c_58])).

tff(c_1337,plain,(
    ! [B_432] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_432,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_432,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_432))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1333,c_1306])).

tff(c_1471,plain,(
    ! [B_460] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_460,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_460,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_460)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1337])).

tff(c_1479,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1471])).

tff(c_1485,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1313,c_1479])).

tff(c_1488,plain,(
    ~ v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1449,c_1485])).

tff(c_1492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_1488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.64  
% 3.46/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.64  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.46/1.64  
% 3.46/1.64  %Foreground sorts:
% 3.46/1.64  
% 3.46/1.64  
% 3.46/1.64  %Background operators:
% 3.46/1.64  
% 3.46/1.64  
% 3.46/1.64  %Foreground operators:
% 3.46/1.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.46/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.46/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.46/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.46/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.46/1.64  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.46/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.46/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.46/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.46/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.46/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.46/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.46/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.46/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.46/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.46/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.64  
% 3.76/1.66  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 3.76/1.66  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.76/1.66  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.76/1.66  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.76/1.66  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 3.76/1.66  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.76/1.66  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.76/1.66  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 3.76/1.66  tff(f_62, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(k6_relat_1(C), D)) <=> (r2_hidden(A, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_relat_1)).
% 3.76/1.66  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.76/1.66  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.76/1.66  tff(c_1020, plain, (![C_353, A_354, B_355]: (v4_relat_1(C_353, A_354) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_354, B_355))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.76/1.66  tff(c_1024, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_1020])).
% 3.76/1.66  tff(c_62, plain, (![C_121, A_122, B_123]: (v1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.76/1.66  tff(c_66, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_62])).
% 3.76/1.66  tff(c_1308, plain, (![A_426, B_427, C_428, D_429]: (k7_relset_1(A_426, B_427, C_428, D_429)=k9_relat_1(C_428, D_429) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_426, B_427))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.76/1.66  tff(c_1311, plain, (![D_429]: (k7_relset_1('#skF_4', '#skF_2', '#skF_5', D_429)=k9_relat_1('#skF_5', D_429))), inference(resolution, [status(thm)], [c_38, c_1308])).
% 3.76/1.66  tff(c_74, plain, (![C_128, A_129, B_130]: (v4_relat_1(C_128, A_129) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.76/1.66  tff(c_78, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_74])).
% 3.76/1.66  tff(c_784, plain, (![A_304, B_305, C_306, D_307]: (k7_relset_1(A_304, B_305, C_306, D_307)=k9_relat_1(C_306, D_307) | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1(A_304, B_305))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.76/1.66  tff(c_787, plain, (![D_307]: (k7_relset_1('#skF_4', '#skF_2', '#skF_5', D_307)=k9_relat_1('#skF_5', D_307))), inference(resolution, [status(thm)], [c_38, c_784])).
% 3.76/1.66  tff(c_461, plain, (![A_233, B_234, C_235, D_236]: (k7_relset_1(A_233, B_234, C_235, D_236)=k9_relat_1(C_235, D_236) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.76/1.66  tff(c_464, plain, (![D_236]: (k7_relset_1('#skF_4', '#skF_2', '#skF_5', D_236)=k9_relat_1('#skF_5', D_236))), inference(resolution, [status(thm)], [c_38, c_461])).
% 3.76/1.66  tff(c_60, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.76/1.66  tff(c_68, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 3.76/1.66  tff(c_52, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | r2_hidden('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.76/1.66  tff(c_84, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 3.76/1.66  tff(c_56, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.76/1.66  tff(c_89, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 3.76/1.66  tff(c_145, plain, (![A_154, B_155, C_156, D_157]: (k7_relset_1(A_154, B_155, C_156, D_157)=k9_relat_1(C_156, D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.76/1.66  tff(c_148, plain, (![D_157]: (k7_relset_1('#skF_4', '#skF_2', '#skF_5', D_157)=k9_relat_1('#skF_5', D_157))), inference(resolution, [status(thm)], [c_38, c_145])).
% 3.76/1.66  tff(c_46, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski(F_118, '#skF_6'), '#skF_5') | ~m1_subset_1(F_118, '#skF_4') | ~r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.76/1.66  tff(c_288, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski(F_118, '#skF_6'), '#skF_5') | ~m1_subset_1(F_118, '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_46])).
% 3.76/1.66  tff(c_289, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_288])).
% 3.76/1.66  tff(c_115, plain, (![A_141, C_142, B_143]: (r2_hidden(A_141, k1_relat_1(C_142)) | ~r2_hidden(k4_tarski(A_141, B_143), C_142) | ~v1_relat_1(C_142))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.76/1.66  tff(c_118, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_89, c_115])).
% 3.76/1.66  tff(c_121, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_118])).
% 3.76/1.66  tff(c_307, plain, (![A_199, C_200, B_201, D_202]: (r2_hidden(A_199, k9_relat_1(C_200, B_201)) | ~r2_hidden(D_202, B_201) | ~r2_hidden(k4_tarski(D_202, A_199), C_200) | ~r2_hidden(D_202, k1_relat_1(C_200)) | ~v1_relat_1(C_200))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.76/1.66  tff(c_338, plain, (![A_203, C_204]: (r2_hidden(A_203, k9_relat_1(C_204, '#skF_3')) | ~r2_hidden(k4_tarski('#skF_7', A_203), C_204) | ~r2_hidden('#skF_7', k1_relat_1(C_204)) | ~v1_relat_1(C_204))), inference(resolution, [status(thm)], [c_84, c_307])).
% 3.76/1.66  tff(c_345, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_89, c_338])).
% 3.76/1.66  tff(c_349, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_121, c_345])).
% 3.76/1.66  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_289, c_349])).
% 3.76/1.66  tff(c_403, plain, (![F_209]: (~r2_hidden(F_209, '#skF_3') | ~r2_hidden(k4_tarski(F_209, '#skF_6'), '#skF_5') | ~m1_subset_1(F_209, '#skF_4'))), inference(splitRight, [status(thm)], [c_288])).
% 3.76/1.66  tff(c_410, plain, (~r2_hidden('#skF_7', '#skF_3') | ~m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_89, c_403])).
% 3.76/1.66  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_84, c_410])).
% 3.76/1.66  tff(c_418, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_56])).
% 3.76/1.66  tff(c_466, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_418])).
% 3.76/1.66  tff(c_12, plain, (![A_5, B_6, C_7]: (r2_hidden(k4_tarski('#skF_1'(A_5, B_6, C_7), A_5), C_7) | ~r2_hidden(A_5, k9_relat_1(C_7, B_6)) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.76/1.66  tff(c_6, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.76/1.66  tff(c_424, plain, (![A_210, B_211]: (k5_relat_1(k6_relat_1(A_210), B_211)=B_211 | ~r1_tarski(k1_relat_1(B_211), A_210) | ~v1_relat_1(B_211))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.76/1.66  tff(c_428, plain, (![A_3, B_4]: (k5_relat_1(k6_relat_1(A_3), B_4)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_6, c_424])).
% 3.76/1.66  tff(c_445, plain, (![A_223, C_224, B_225, D_226]: (r2_hidden(A_223, C_224) | ~r2_hidden(k4_tarski(A_223, B_225), k5_relat_1(k6_relat_1(C_224), D_226)) | ~v1_relat_1(D_226))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.76/1.66  tff(c_592, plain, (![A_259, A_260, B_261, B_262]: (r2_hidden(A_259, A_260) | ~r2_hidden(k4_tarski(A_259, B_261), B_262) | ~v1_relat_1(B_262) | ~v4_relat_1(B_262, A_260) | ~v1_relat_1(B_262))), inference(superposition, [status(thm), theory('equality')], [c_428, c_445])).
% 3.76/1.66  tff(c_599, plain, (![A_263, B_264, C_265, A_266]: (r2_hidden('#skF_1'(A_263, B_264, C_265), A_266) | ~v4_relat_1(C_265, A_266) | ~r2_hidden(A_263, k9_relat_1(C_265, B_264)) | ~v1_relat_1(C_265))), inference(resolution, [status(thm)], [c_12, c_592])).
% 3.76/1.66  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.76/1.66  tff(c_615, plain, (![A_267, B_268, C_269, A_270]: (m1_subset_1('#skF_1'(A_267, B_268, C_269), A_270) | ~v4_relat_1(C_269, A_270) | ~r2_hidden(A_267, k9_relat_1(C_269, B_268)) | ~v1_relat_1(C_269))), inference(resolution, [status(thm)], [c_599, c_2])).
% 3.76/1.66  tff(c_620, plain, (![A_270]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_270) | ~v4_relat_1('#skF_5', A_270) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_466, c_615])).
% 3.76/1.66  tff(c_630, plain, (![A_270]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_270) | ~v4_relat_1('#skF_5', A_270))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_620])).
% 3.76/1.66  tff(c_10, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_1'(A_5, B_6, C_7), B_6) | ~r2_hidden(A_5, k9_relat_1(C_7, B_6)) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.76/1.66  tff(c_419, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 3.76/1.66  tff(c_54, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski(F_118, '#skF_6'), '#skF_5') | ~m1_subset_1(F_118, '#skF_4') | r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.76/1.66  tff(c_509, plain, (![F_241]: (~r2_hidden(F_241, '#skF_3') | ~r2_hidden(k4_tarski(F_241, '#skF_6'), '#skF_5') | ~m1_subset_1(F_241, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_419, c_54])).
% 3.76/1.66  tff(c_513, plain, (![B_6]: (~r2_hidden('#skF_1'('#skF_6', B_6, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_6, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_6)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_509])).
% 3.76/1.66  tff(c_686, plain, (![B_280]: (~r2_hidden('#skF_1'('#skF_6', B_280, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_280, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_280)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_513])).
% 3.76/1.66  tff(c_694, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_686])).
% 3.76/1.66  tff(c_700, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_466, c_694])).
% 3.76/1.66  tff(c_740, plain, (~v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_630, c_700])).
% 3.76/1.66  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_740])).
% 3.76/1.66  tff(c_745, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 3.76/1.66  tff(c_794, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_745])).
% 3.76/1.66  tff(c_753, plain, (![A_289, B_290]: (k5_relat_1(k6_relat_1(A_289), B_290)=B_290 | ~r1_tarski(k1_relat_1(B_290), A_289) | ~v1_relat_1(B_290))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.76/1.66  tff(c_757, plain, (![A_3, B_4]: (k5_relat_1(k6_relat_1(A_3), B_4)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_6, c_753])).
% 3.76/1.66  tff(c_768, plain, (![A_293, C_294, B_295, D_296]: (r2_hidden(A_293, C_294) | ~r2_hidden(k4_tarski(A_293, B_295), k5_relat_1(k6_relat_1(C_294), D_296)) | ~v1_relat_1(D_296))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.76/1.66  tff(c_897, plain, (![A_328, A_329, B_330, B_331]: (r2_hidden(A_328, A_329) | ~r2_hidden(k4_tarski(A_328, B_330), B_331) | ~v1_relat_1(B_331) | ~v4_relat_1(B_331, A_329) | ~v1_relat_1(B_331))), inference(superposition, [status(thm), theory('equality')], [c_757, c_768])).
% 3.76/1.66  tff(c_901, plain, (![A_332, B_333, C_334, A_335]: (r2_hidden('#skF_1'(A_332, B_333, C_334), A_335) | ~v4_relat_1(C_334, A_335) | ~r2_hidden(A_332, k9_relat_1(C_334, B_333)) | ~v1_relat_1(C_334))), inference(resolution, [status(thm)], [c_12, c_897])).
% 3.76/1.66  tff(c_915, plain, (![A_336, B_337, C_338, A_339]: (m1_subset_1('#skF_1'(A_336, B_337, C_338), A_339) | ~v4_relat_1(C_338, A_339) | ~r2_hidden(A_336, k9_relat_1(C_338, B_337)) | ~v1_relat_1(C_338))), inference(resolution, [status(thm)], [c_901, c_2])).
% 3.76/1.66  tff(c_923, plain, (![A_339]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_339) | ~v4_relat_1('#skF_5', A_339) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_794, c_915])).
% 3.76/1.66  tff(c_931, plain, (![A_339]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_339) | ~v4_relat_1('#skF_5', A_339))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_923])).
% 3.76/1.66  tff(c_820, plain, (![A_319, B_320, C_321]: (r2_hidden(k4_tarski('#skF_1'(A_319, B_320, C_321), A_319), C_321) | ~r2_hidden(A_319, k9_relat_1(C_321, B_320)) | ~v1_relat_1(C_321))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.76/1.66  tff(c_746, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 3.76/1.66  tff(c_50, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski(F_118, '#skF_6'), '#skF_5') | ~m1_subset_1(F_118, '#skF_4') | r2_hidden('#skF_7', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.76/1.66  tff(c_782, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski(F_118, '#skF_6'), '#skF_5') | ~m1_subset_1(F_118, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_746, c_50])).
% 3.76/1.66  tff(c_828, plain, (![B_320]: (~r2_hidden('#skF_1'('#skF_6', B_320, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_320, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_320)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_820, c_782])).
% 3.76/1.66  tff(c_982, plain, (![B_347]: (~r2_hidden('#skF_1'('#skF_6', B_347, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_347, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_347)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_828])).
% 3.76/1.66  tff(c_990, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_982])).
% 3.76/1.66  tff(c_996, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_794, c_990])).
% 3.76/1.66  tff(c_999, plain, (~v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_931, c_996])).
% 3.76/1.66  tff(c_1003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_999])).
% 3.76/1.66  tff(c_1004, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 3.76/1.66  tff(c_1313, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1311, c_1004])).
% 3.76/1.66  tff(c_1028, plain, (![A_362, B_363]: (k5_relat_1(k6_relat_1(A_362), B_363)=B_363 | ~r1_tarski(k1_relat_1(B_363), A_362) | ~v1_relat_1(B_363))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.76/1.66  tff(c_1032, plain, (![A_3, B_4]: (k5_relat_1(k6_relat_1(A_3), B_4)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_6, c_1028])).
% 3.76/1.66  tff(c_1048, plain, (![A_369, C_370, B_371, D_372]: (r2_hidden(A_369, C_370) | ~r2_hidden(k4_tarski(A_369, B_371), k5_relat_1(k6_relat_1(C_370), D_372)) | ~v1_relat_1(D_372))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.76/1.66  tff(c_1413, plain, (![A_447, A_448, B_449, B_450]: (r2_hidden(A_447, A_448) | ~r2_hidden(k4_tarski(A_447, B_449), B_450) | ~v1_relat_1(B_450) | ~v4_relat_1(B_450, A_448) | ~v1_relat_1(B_450))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_1048])).
% 3.76/1.66  tff(c_1419, plain, (![A_451, B_452, C_453, A_454]: (r2_hidden('#skF_1'(A_451, B_452, C_453), A_454) | ~v4_relat_1(C_453, A_454) | ~r2_hidden(A_451, k9_relat_1(C_453, B_452)) | ~v1_relat_1(C_453))), inference(resolution, [status(thm)], [c_12, c_1413])).
% 3.76/1.66  tff(c_1433, plain, (![A_455, B_456, C_457, A_458]: (m1_subset_1('#skF_1'(A_455, B_456, C_457), A_458) | ~v4_relat_1(C_457, A_458) | ~r2_hidden(A_455, k9_relat_1(C_457, B_456)) | ~v1_relat_1(C_457))), inference(resolution, [status(thm)], [c_1419, c_2])).
% 3.76/1.66  tff(c_1441, plain, (![A_458]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_458) | ~v4_relat_1('#skF_5', A_458) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1313, c_1433])).
% 3.76/1.66  tff(c_1449, plain, (![A_458]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_458) | ~v4_relat_1('#skF_5', A_458))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1441])).
% 3.76/1.66  tff(c_1333, plain, (![A_431, B_432, C_433]: (r2_hidden(k4_tarski('#skF_1'(A_431, B_432, C_433), A_431), C_433) | ~r2_hidden(A_431, k9_relat_1(C_433, B_432)) | ~v1_relat_1(C_433))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.76/1.66  tff(c_1005, plain, (~m1_subset_1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 3.76/1.66  tff(c_58, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski(F_118, '#skF_6'), '#skF_5') | ~m1_subset_1(F_118, '#skF_4') | m1_subset_1('#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.76/1.66  tff(c_1306, plain, (![F_118]: (~r2_hidden(F_118, '#skF_3') | ~r2_hidden(k4_tarski(F_118, '#skF_6'), '#skF_5') | ~m1_subset_1(F_118, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1005, c_58])).
% 3.76/1.66  tff(c_1337, plain, (![B_432]: (~r2_hidden('#skF_1'('#skF_6', B_432, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_432, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_432)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1333, c_1306])).
% 3.76/1.66  tff(c_1471, plain, (![B_460]: (~r2_hidden('#skF_1'('#skF_6', B_460, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_460, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_460)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1337])).
% 3.76/1.66  tff(c_1479, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_1471])).
% 3.76/1.66  tff(c_1485, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1313, c_1479])).
% 3.76/1.66  tff(c_1488, plain, (~v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1449, c_1485])).
% 3.76/1.66  tff(c_1492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1024, c_1488])).
% 3.76/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.66  
% 3.76/1.66  Inference rules
% 3.76/1.66  ----------------------
% 3.76/1.66  #Ref     : 0
% 3.76/1.66  #Sup     : 297
% 3.76/1.66  #Fact    : 0
% 3.76/1.66  #Define  : 0
% 3.76/1.66  #Split   : 8
% 3.76/1.66  #Chain   : 0
% 3.76/1.66  #Close   : 0
% 3.76/1.66  
% 3.76/1.66  Ordering : KBO
% 3.76/1.66  
% 3.76/1.66  Simplification rules
% 3.76/1.66  ----------------------
% 3.76/1.66  #Subsume      : 22
% 3.76/1.66  #Demod        : 74
% 3.76/1.66  #Tautology    : 52
% 3.76/1.66  #SimpNegUnit  : 5
% 3.76/1.66  #BackRed      : 8
% 3.76/1.66  
% 3.76/1.66  #Partial instantiations: 0
% 3.76/1.66  #Strategies tried      : 1
% 3.76/1.66  
% 3.76/1.66  Timing (in seconds)
% 3.76/1.66  ----------------------
% 3.76/1.67  Preprocessing        : 0.32
% 3.76/1.67  Parsing              : 0.16
% 3.76/1.67  CNF conversion       : 0.03
% 3.76/1.67  Main loop            : 0.50
% 3.76/1.67  Inferencing          : 0.20
% 3.76/1.67  Reduction            : 0.14
% 3.76/1.67  Demodulation         : 0.09
% 3.76/1.67  BG Simplification    : 0.03
% 3.76/1.67  Subsumption          : 0.09
% 3.76/1.67  Abstraction          : 0.02
% 3.76/1.67  MUC search           : 0.00
% 3.76/1.67  Cooper               : 0.00
% 3.76/1.67  Total                : 0.87
% 3.76/1.67  Index Insertion      : 0.00
% 3.76/1.67  Index Deletion       : 0.00
% 3.76/1.67  Index Matching       : 0.00
% 3.76/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
