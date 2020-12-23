%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:42 EST 2020

% Result     : Theorem 34.70s
% Output     : CNFRefutation 34.70s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 144 expanded)
%              Number of leaves         :   29 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  213 ( 391 expanded)
%              Number of equality atoms :   24 (  53 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_3 > #skF_13 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
             => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_132,B_133] :
      ( ~ r2_hidden('#skF_1'(A_132,B_133),B_133)
      | r1_tarski(A_132,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_48,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ! [A_124,B_125] :
      ( v1_relat_1(k5_relat_1(A_124,B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    r1_tarski(k1_relat_1('#skF_12'),k2_relat_1('#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_76,plain,(
    ! [A_151,C_152] :
      ( r2_hidden(k4_tarski('#skF_5'(A_151,k2_relat_1(A_151),C_152),C_152),A_151)
      | ~ r2_hidden(C_152,k2_relat_1(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [A_170,C_171,B_172] :
      ( r2_hidden(k4_tarski('#skF_5'(A_170,k2_relat_1(A_170),C_171),C_171),B_172)
      | ~ r1_tarski(A_170,B_172)
      | ~ r2_hidden(C_171,k2_relat_1(A_170)) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_42,plain,(
    ! [A_126,C_128,B_127] :
      ( r2_hidden(A_126,k1_relat_1(C_128))
      | ~ r2_hidden(k4_tarski(A_126,B_127),C_128)
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_616,plain,(
    ! [A_221,C_222,B_223] :
      ( r2_hidden('#skF_5'(A_221,k2_relat_1(A_221),C_222),k1_relat_1(B_223))
      | ~ v1_relat_1(B_223)
      | ~ r1_tarski(A_221,B_223)
      | ~ r2_hidden(C_222,k2_relat_1(A_221)) ) ),
    inference(resolution,[status(thm)],[c_131,c_42])).

tff(c_3216,plain,(
    ! [A_423,C_424,B_425,B_426] :
      ( r2_hidden('#skF_5'(A_423,k2_relat_1(A_423),C_424),B_425)
      | ~ r1_tarski(k1_relat_1(B_426),B_425)
      | ~ v1_relat_1(B_426)
      | ~ r1_tarski(A_423,B_426)
      | ~ r2_hidden(C_424,k2_relat_1(A_423)) ) ),
    inference(resolution,[status(thm)],[c_616,c_2])).

tff(c_3224,plain,(
    ! [A_423,C_424] :
      ( r2_hidden('#skF_5'(A_423,k2_relat_1(A_423),C_424),k2_relat_1('#skF_13'))
      | ~ v1_relat_1('#skF_12')
      | ~ r1_tarski(A_423,'#skF_12')
      | ~ r2_hidden(C_424,k2_relat_1(A_423)) ) ),
    inference(resolution,[status(thm)],[c_46,c_3216])).

tff(c_3229,plain,(
    ! [A_423,C_424] :
      ( r2_hidden('#skF_5'(A_423,k2_relat_1(A_423),C_424),k2_relat_1('#skF_13'))
      | ~ r1_tarski(A_423,'#skF_12')
      | ~ r2_hidden(C_424,k2_relat_1(A_423)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3224])).

tff(c_8,plain,(
    ! [A_6,C_21] :
      ( r2_hidden(k4_tarski('#skF_5'(A_6,k2_relat_1(A_6),C_21),C_21),A_6)
      | ~ r2_hidden(C_21,k2_relat_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_391,plain,(
    ! [B_200,F_203,D_199,E_202,A_201] :
      ( r2_hidden(k4_tarski(D_199,E_202),k5_relat_1(A_201,B_200))
      | ~ r2_hidden(k4_tarski(F_203,E_202),B_200)
      | ~ r2_hidden(k4_tarski(D_199,F_203),A_201)
      | ~ v1_relat_1(k5_relat_1(A_201,B_200))
      | ~ v1_relat_1(B_200)
      | ~ v1_relat_1(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3633,plain,(
    ! [D_450,C_451,A_452,A_453] :
      ( r2_hidden(k4_tarski(D_450,C_451),k5_relat_1(A_452,A_453))
      | ~ r2_hidden(k4_tarski(D_450,'#skF_5'(A_453,k2_relat_1(A_453),C_451)),A_452)
      | ~ v1_relat_1(k5_relat_1(A_452,A_453))
      | ~ v1_relat_1(A_453)
      | ~ v1_relat_1(A_452)
      | ~ r2_hidden(C_451,k2_relat_1(A_453)) ) ),
    inference(resolution,[status(thm)],[c_8,c_391])).

tff(c_61556,plain,(
    ! [A_2269,A_2270,C_2271] :
      ( r2_hidden(k4_tarski('#skF_5'(A_2269,k2_relat_1(A_2269),'#skF_5'(A_2270,k2_relat_1(A_2270),C_2271)),C_2271),k5_relat_1(A_2269,A_2270))
      | ~ v1_relat_1(k5_relat_1(A_2269,A_2270))
      | ~ v1_relat_1(A_2270)
      | ~ v1_relat_1(A_2269)
      | ~ r2_hidden(C_2271,k2_relat_1(A_2270))
      | ~ r2_hidden('#skF_5'(A_2270,k2_relat_1(A_2270),C_2271),k2_relat_1(A_2269)) ) ),
    inference(resolution,[status(thm)],[c_8,c_3633])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k2_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(D_24,C_21),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_61657,plain,(
    ! [C_2272,A_2273,A_2274] :
      ( r2_hidden(C_2272,k2_relat_1(k5_relat_1(A_2273,A_2274)))
      | ~ v1_relat_1(k5_relat_1(A_2273,A_2274))
      | ~ v1_relat_1(A_2274)
      | ~ v1_relat_1(A_2273)
      | ~ r2_hidden(C_2272,k2_relat_1(A_2274))
      | ~ r2_hidden('#skF_5'(A_2274,k2_relat_1(A_2274),C_2272),k2_relat_1(A_2273)) ) ),
    inference(resolution,[status(thm)],[c_61556,c_10])).

tff(c_61667,plain,(
    ! [C_424,A_423] :
      ( r2_hidden(C_424,k2_relat_1(k5_relat_1('#skF_13',A_423)))
      | ~ v1_relat_1(k5_relat_1('#skF_13',A_423))
      | ~ v1_relat_1(A_423)
      | ~ v1_relat_1('#skF_13')
      | ~ r1_tarski(A_423,'#skF_12')
      | ~ r2_hidden(C_424,k2_relat_1(A_423)) ) ),
    inference(resolution,[status(thm)],[c_3229,c_61657])).

tff(c_61696,plain,(
    ! [C_2275,A_2276] :
      ( r2_hidden(C_2275,k2_relat_1(k5_relat_1('#skF_13',A_2276)))
      | ~ v1_relat_1(k5_relat_1('#skF_13',A_2276))
      | ~ v1_relat_1(A_2276)
      | ~ r1_tarski(A_2276,'#skF_12')
      | ~ r2_hidden(C_2275,k2_relat_1(A_2276)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_61667])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63616,plain,(
    ! [A_2301,A_2302] :
      ( r1_tarski(A_2301,k2_relat_1(k5_relat_1('#skF_13',A_2302)))
      | ~ v1_relat_1(k5_relat_1('#skF_13',A_2302))
      | ~ v1_relat_1(A_2302)
      | ~ r1_tarski(A_2302,'#skF_12')
      | ~ r2_hidden('#skF_1'(A_2301,k2_relat_1(k5_relat_1('#skF_13',A_2302))),k2_relat_1(A_2302)) ) ),
    inference(resolution,[status(thm)],[c_61696,c_4])).

tff(c_63805,plain,(
    ! [A_2307] :
      ( ~ v1_relat_1(k5_relat_1('#skF_13',A_2307))
      | ~ v1_relat_1(A_2307)
      | ~ r1_tarski(A_2307,'#skF_12')
      | r1_tarski(k2_relat_1(A_2307),k2_relat_1(k5_relat_1('#skF_13',A_2307))) ) ),
    inference(resolution,[status(thm)],[c_6,c_63616])).

tff(c_578,plain,(
    ! [D_217,B_218,A_219,E_220] :
      ( r2_hidden(k4_tarski('#skF_6'(D_217,B_218,A_219,E_220,k5_relat_1(A_219,B_218)),E_220),B_218)
      | ~ r2_hidden(k4_tarski(D_217,E_220),k5_relat_1(A_219,B_218))
      | ~ v1_relat_1(k5_relat_1(A_219,B_218))
      | ~ v1_relat_1(B_218)
      | ~ v1_relat_1(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1316,plain,(
    ! [E_289,B_290,D_291,A_292] :
      ( r2_hidden(E_289,k2_relat_1(B_290))
      | ~ r2_hidden(k4_tarski(D_291,E_289),k5_relat_1(A_292,B_290))
      | ~ v1_relat_1(k5_relat_1(A_292,B_290))
      | ~ v1_relat_1(B_290)
      | ~ v1_relat_1(A_292) ) ),
    inference(resolution,[status(thm)],[c_578,c_10])).

tff(c_1384,plain,(
    ! [C_295,B_296,A_297] :
      ( r2_hidden(C_295,k2_relat_1(B_296))
      | ~ v1_relat_1(k5_relat_1(A_297,B_296))
      | ~ v1_relat_1(B_296)
      | ~ v1_relat_1(A_297)
      | ~ r2_hidden(C_295,k2_relat_1(k5_relat_1(A_297,B_296))) ) ),
    inference(resolution,[status(thm)],[c_8,c_1316])).

tff(c_15988,plain,(
    ! [A_933,B_934,B_935] :
      ( r2_hidden('#skF_1'(k2_relat_1(k5_relat_1(A_933,B_934)),B_935),k2_relat_1(B_934))
      | ~ v1_relat_1(k5_relat_1(A_933,B_934))
      | ~ v1_relat_1(B_934)
      | ~ v1_relat_1(A_933)
      | r1_tarski(k2_relat_1(k5_relat_1(A_933,B_934)),B_935) ) ),
    inference(resolution,[status(thm)],[c_6,c_1384])).

tff(c_16048,plain,(
    ! [A_936,B_937] :
      ( ~ v1_relat_1(k5_relat_1(A_936,B_937))
      | ~ v1_relat_1(B_937)
      | ~ v1_relat_1(A_936)
      | r1_tarski(k2_relat_1(k5_relat_1(A_936,B_937)),k2_relat_1(B_937)) ) ),
    inference(resolution,[status(thm)],[c_15988,c_4])).

tff(c_192,plain,(
    ! [A_179,B_180] :
      ( r2_hidden(k4_tarski('#skF_3'(A_179,B_180),'#skF_2'(A_179,B_180)),A_179)
      | r2_hidden('#skF_4'(A_179,B_180),B_180)
      | k2_relat_1(A_179) = B_180 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_317,plain,(
    ! [A_188,B_189] :
      ( r2_hidden('#skF_2'(A_188,B_189),k2_relat_1(A_188))
      | r2_hidden('#skF_4'(A_188,B_189),B_189)
      | k2_relat_1(A_188) = B_189 ) ),
    inference(resolution,[status(thm)],[c_192,c_10])).

tff(c_678,plain,(
    ! [A_229,B_230,B_231] :
      ( r2_hidden('#skF_2'(A_229,B_230),B_231)
      | ~ r1_tarski(k2_relat_1(A_229),B_231)
      | r2_hidden('#skF_4'(A_229,B_230),B_230)
      | k2_relat_1(A_229) = B_230 ) ),
    inference(resolution,[status(thm)],[c_317,c_2])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r2_hidden('#skF_4'(A_6,B_7),B_7)
      | k2_relat_1(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_710,plain,(
    ! [A_232,B_233] :
      ( ~ r1_tarski(k2_relat_1(A_232),B_233)
      | r2_hidden('#skF_4'(A_232,B_233),B_233)
      | k2_relat_1(A_232) = B_233 ) ),
    inference(resolution,[status(thm)],[c_678,c_16])).

tff(c_721,plain,(
    ! [A_232,B_233,B_2] :
      ( r2_hidden('#skF_4'(A_232,B_233),B_2)
      | ~ r1_tarski(B_233,B_2)
      | ~ r1_tarski(k2_relat_1(A_232),B_233)
      | k2_relat_1(A_232) = B_233 ) ),
    inference(resolution,[status(thm)],[c_710,c_2])).

tff(c_342,plain,(
    ! [A_190,B_191,D_192] :
      ( r2_hidden(k4_tarski('#skF_3'(A_190,B_191),'#skF_2'(A_190,B_191)),A_190)
      | ~ r2_hidden(k4_tarski(D_192,'#skF_4'(A_190,B_191)),A_190)
      | k2_relat_1(A_190) = B_191 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1118,plain,(
    ! [A_259,B_260] :
      ( r2_hidden(k4_tarski('#skF_3'(A_259,B_260),'#skF_2'(A_259,B_260)),A_259)
      | k2_relat_1(A_259) = B_260
      | ~ r2_hidden('#skF_4'(A_259,B_260),k2_relat_1(A_259)) ) ),
    inference(resolution,[status(thm)],[c_8,c_342])).

tff(c_1137,plain,(
    ! [A_261,B_262] :
      ( r2_hidden('#skF_2'(A_261,B_262),k2_relat_1(A_261))
      | k2_relat_1(A_261) = B_262
      | ~ r2_hidden('#skF_4'(A_261,B_262),k2_relat_1(A_261)) ) ),
    inference(resolution,[status(thm)],[c_1118,c_10])).

tff(c_1165,plain,(
    ! [A_268,B_269,B_270] :
      ( r2_hidden('#skF_2'(A_268,B_269),B_270)
      | ~ r1_tarski(k2_relat_1(A_268),B_270)
      | k2_relat_1(A_268) = B_269
      | ~ r2_hidden('#skF_4'(A_268,B_269),k2_relat_1(A_268)) ) ),
    inference(resolution,[status(thm)],[c_1137,c_2])).

tff(c_3317,plain,(
    ! [A_435,B_436,B_437] :
      ( r2_hidden('#skF_2'(A_435,B_436),B_437)
      | ~ r1_tarski(k2_relat_1(A_435),B_437)
      | ~ r1_tarski(B_436,k2_relat_1(A_435))
      | ~ r1_tarski(k2_relat_1(A_435),B_436)
      | k2_relat_1(A_435) = B_436 ) ),
    inference(resolution,[status(thm)],[c_721,c_1165])).

tff(c_12,plain,(
    ! [A_6,B_7,D_20] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden(k4_tarski(D_20,'#skF_4'(A_6,B_7)),A_6)
      | k2_relat_1(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3351,plain,(
    ! [D_438,A_439,B_440] :
      ( ~ r2_hidden(k4_tarski(D_438,'#skF_4'(A_439,B_440)),A_439)
      | ~ r1_tarski(B_440,k2_relat_1(A_439))
      | ~ r1_tarski(k2_relat_1(A_439),B_440)
      | k2_relat_1(A_439) = B_440 ) ),
    inference(resolution,[status(thm)],[c_3317,c_12])).

tff(c_3434,plain,(
    ! [B_444,A_445] :
      ( ~ r1_tarski(B_444,k2_relat_1(A_445))
      | ~ r1_tarski(k2_relat_1(A_445),B_444)
      | k2_relat_1(A_445) = B_444
      | ~ r2_hidden('#skF_4'(A_445,B_444),k2_relat_1(A_445)) ) ),
    inference(resolution,[status(thm)],[c_8,c_3351])).

tff(c_3559,plain,(
    ! [B_233,A_232] :
      ( ~ r1_tarski(B_233,k2_relat_1(A_232))
      | ~ r1_tarski(k2_relat_1(A_232),B_233)
      | k2_relat_1(A_232) = B_233 ) ),
    inference(resolution,[status(thm)],[c_721,c_3434])).

tff(c_16188,plain,(
    ! [B_937,A_936] :
      ( ~ r1_tarski(k2_relat_1(B_937),k2_relat_1(k5_relat_1(A_936,B_937)))
      | k2_relat_1(k5_relat_1(A_936,B_937)) = k2_relat_1(B_937)
      | ~ v1_relat_1(k5_relat_1(A_936,B_937))
      | ~ v1_relat_1(B_937)
      | ~ v1_relat_1(A_936) ) ),
    inference(resolution,[status(thm)],[c_16048,c_3559])).

tff(c_64061,plain,(
    ! [A_2307] :
      ( k2_relat_1(k5_relat_1('#skF_13',A_2307)) = k2_relat_1(A_2307)
      | ~ v1_relat_1('#skF_13')
      | ~ v1_relat_1(k5_relat_1('#skF_13',A_2307))
      | ~ v1_relat_1(A_2307)
      | ~ r1_tarski(A_2307,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_63805,c_16188])).

tff(c_64354,plain,(
    ! [A_2308] :
      ( k2_relat_1(k5_relat_1('#skF_13',A_2308)) = k2_relat_1(A_2308)
      | ~ v1_relat_1(k5_relat_1('#skF_13',A_2308))
      | ~ v1_relat_1(A_2308)
      | ~ r1_tarski(A_2308,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_64061])).

tff(c_64358,plain,(
    ! [B_125] :
      ( k2_relat_1(k5_relat_1('#skF_13',B_125)) = k2_relat_1(B_125)
      | ~ r1_tarski(B_125,'#skF_12')
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_38,c_64354])).

tff(c_64362,plain,(
    ! [B_2309] :
      ( k2_relat_1(k5_relat_1('#skF_13',B_2309)) = k2_relat_1(B_2309)
      | ~ r1_tarski(B_2309,'#skF_12')
      | ~ v1_relat_1(B_2309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_64358])).

tff(c_44,plain,(
    k2_relat_1(k5_relat_1('#skF_13','#skF_12')) != k2_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_65653,plain,
    ( ~ r1_tarski('#skF_12','#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_64362,c_44])).

tff(c_65748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_57,c_65653])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.70/25.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.70/25.02  
% 34.70/25.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.70/25.02  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_3 > #skF_13 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4 > #skF_10
% 34.70/25.02  
% 34.70/25.02  %Foreground sorts:
% 34.70/25.02  
% 34.70/25.02  
% 34.70/25.02  %Background operators:
% 34.70/25.02  
% 34.70/25.02  
% 34.70/25.02  %Foreground operators:
% 34.70/25.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.70/25.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 34.70/25.02  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 34.70/25.02  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 34.70/25.02  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i) > $i).
% 34.70/25.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 34.70/25.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 34.70/25.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 34.70/25.02  tff('#skF_13', type, '#skF_13': $i).
% 34.70/25.02  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 34.70/25.02  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 34.70/25.02  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 34.70/25.02  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 34.70/25.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.70/25.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 34.70/25.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.70/25.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 34.70/25.02  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 34.70/25.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 34.70/25.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 34.70/25.02  tff('#skF_12', type, '#skF_12': $i).
% 34.70/25.02  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 34.70/25.02  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 34.70/25.02  
% 34.70/25.04  tff(f_82, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 34.70/25.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 34.70/25.04  tff(f_64, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 34.70/25.04  tff(f_40, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 34.70/25.04  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 34.70/25.04  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 34.70/25.04  tff(c_50, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_82])).
% 34.70/25.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.70/25.04  tff(c_52, plain, (![A_132, B_133]: (~r2_hidden('#skF_1'(A_132, B_133), B_133) | r1_tarski(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.70/25.04  tff(c_57, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_52])).
% 34.70/25.04  tff(c_48, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_82])).
% 34.70/25.04  tff(c_38, plain, (![A_124, B_125]: (v1_relat_1(k5_relat_1(A_124, B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_64])).
% 34.70/25.04  tff(c_46, plain, (r1_tarski(k1_relat_1('#skF_12'), k2_relat_1('#skF_13'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 34.70/25.04  tff(c_76, plain, (![A_151, C_152]: (r2_hidden(k4_tarski('#skF_5'(A_151, k2_relat_1(A_151), C_152), C_152), A_151) | ~r2_hidden(C_152, k2_relat_1(A_151)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 34.70/25.04  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.70/25.04  tff(c_131, plain, (![A_170, C_171, B_172]: (r2_hidden(k4_tarski('#skF_5'(A_170, k2_relat_1(A_170), C_171), C_171), B_172) | ~r1_tarski(A_170, B_172) | ~r2_hidden(C_171, k2_relat_1(A_170)))), inference(resolution, [status(thm)], [c_76, c_2])).
% 34.70/25.04  tff(c_42, plain, (![A_126, C_128, B_127]: (r2_hidden(A_126, k1_relat_1(C_128)) | ~r2_hidden(k4_tarski(A_126, B_127), C_128) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_72])).
% 34.70/25.04  tff(c_616, plain, (![A_221, C_222, B_223]: (r2_hidden('#skF_5'(A_221, k2_relat_1(A_221), C_222), k1_relat_1(B_223)) | ~v1_relat_1(B_223) | ~r1_tarski(A_221, B_223) | ~r2_hidden(C_222, k2_relat_1(A_221)))), inference(resolution, [status(thm)], [c_131, c_42])).
% 34.70/25.04  tff(c_3216, plain, (![A_423, C_424, B_425, B_426]: (r2_hidden('#skF_5'(A_423, k2_relat_1(A_423), C_424), B_425) | ~r1_tarski(k1_relat_1(B_426), B_425) | ~v1_relat_1(B_426) | ~r1_tarski(A_423, B_426) | ~r2_hidden(C_424, k2_relat_1(A_423)))), inference(resolution, [status(thm)], [c_616, c_2])).
% 34.70/25.04  tff(c_3224, plain, (![A_423, C_424]: (r2_hidden('#skF_5'(A_423, k2_relat_1(A_423), C_424), k2_relat_1('#skF_13')) | ~v1_relat_1('#skF_12') | ~r1_tarski(A_423, '#skF_12') | ~r2_hidden(C_424, k2_relat_1(A_423)))), inference(resolution, [status(thm)], [c_46, c_3216])).
% 34.70/25.04  tff(c_3229, plain, (![A_423, C_424]: (r2_hidden('#skF_5'(A_423, k2_relat_1(A_423), C_424), k2_relat_1('#skF_13')) | ~r1_tarski(A_423, '#skF_12') | ~r2_hidden(C_424, k2_relat_1(A_423)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3224])).
% 34.70/25.04  tff(c_8, plain, (![A_6, C_21]: (r2_hidden(k4_tarski('#skF_5'(A_6, k2_relat_1(A_6), C_21), C_21), A_6) | ~r2_hidden(C_21, k2_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 34.70/25.04  tff(c_391, plain, (![B_200, F_203, D_199, E_202, A_201]: (r2_hidden(k4_tarski(D_199, E_202), k5_relat_1(A_201, B_200)) | ~r2_hidden(k4_tarski(F_203, E_202), B_200) | ~r2_hidden(k4_tarski(D_199, F_203), A_201) | ~v1_relat_1(k5_relat_1(A_201, B_200)) | ~v1_relat_1(B_200) | ~v1_relat_1(A_201))), inference(cnfTransformation, [status(thm)], [f_58])).
% 34.70/25.04  tff(c_3633, plain, (![D_450, C_451, A_452, A_453]: (r2_hidden(k4_tarski(D_450, C_451), k5_relat_1(A_452, A_453)) | ~r2_hidden(k4_tarski(D_450, '#skF_5'(A_453, k2_relat_1(A_453), C_451)), A_452) | ~v1_relat_1(k5_relat_1(A_452, A_453)) | ~v1_relat_1(A_453) | ~v1_relat_1(A_452) | ~r2_hidden(C_451, k2_relat_1(A_453)))), inference(resolution, [status(thm)], [c_8, c_391])).
% 34.70/25.04  tff(c_61556, plain, (![A_2269, A_2270, C_2271]: (r2_hidden(k4_tarski('#skF_5'(A_2269, k2_relat_1(A_2269), '#skF_5'(A_2270, k2_relat_1(A_2270), C_2271)), C_2271), k5_relat_1(A_2269, A_2270)) | ~v1_relat_1(k5_relat_1(A_2269, A_2270)) | ~v1_relat_1(A_2270) | ~v1_relat_1(A_2269) | ~r2_hidden(C_2271, k2_relat_1(A_2270)) | ~r2_hidden('#skF_5'(A_2270, k2_relat_1(A_2270), C_2271), k2_relat_1(A_2269)))), inference(resolution, [status(thm)], [c_8, c_3633])).
% 34.70/25.04  tff(c_10, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k2_relat_1(A_6)) | ~r2_hidden(k4_tarski(D_24, C_21), A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 34.70/25.04  tff(c_61657, plain, (![C_2272, A_2273, A_2274]: (r2_hidden(C_2272, k2_relat_1(k5_relat_1(A_2273, A_2274))) | ~v1_relat_1(k5_relat_1(A_2273, A_2274)) | ~v1_relat_1(A_2274) | ~v1_relat_1(A_2273) | ~r2_hidden(C_2272, k2_relat_1(A_2274)) | ~r2_hidden('#skF_5'(A_2274, k2_relat_1(A_2274), C_2272), k2_relat_1(A_2273)))), inference(resolution, [status(thm)], [c_61556, c_10])).
% 34.70/25.04  tff(c_61667, plain, (![C_424, A_423]: (r2_hidden(C_424, k2_relat_1(k5_relat_1('#skF_13', A_423))) | ~v1_relat_1(k5_relat_1('#skF_13', A_423)) | ~v1_relat_1(A_423) | ~v1_relat_1('#skF_13') | ~r1_tarski(A_423, '#skF_12') | ~r2_hidden(C_424, k2_relat_1(A_423)))), inference(resolution, [status(thm)], [c_3229, c_61657])).
% 34.70/25.04  tff(c_61696, plain, (![C_2275, A_2276]: (r2_hidden(C_2275, k2_relat_1(k5_relat_1('#skF_13', A_2276))) | ~v1_relat_1(k5_relat_1('#skF_13', A_2276)) | ~v1_relat_1(A_2276) | ~r1_tarski(A_2276, '#skF_12') | ~r2_hidden(C_2275, k2_relat_1(A_2276)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_61667])).
% 34.70/25.04  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.70/25.04  tff(c_63616, plain, (![A_2301, A_2302]: (r1_tarski(A_2301, k2_relat_1(k5_relat_1('#skF_13', A_2302))) | ~v1_relat_1(k5_relat_1('#skF_13', A_2302)) | ~v1_relat_1(A_2302) | ~r1_tarski(A_2302, '#skF_12') | ~r2_hidden('#skF_1'(A_2301, k2_relat_1(k5_relat_1('#skF_13', A_2302))), k2_relat_1(A_2302)))), inference(resolution, [status(thm)], [c_61696, c_4])).
% 34.70/25.04  tff(c_63805, plain, (![A_2307]: (~v1_relat_1(k5_relat_1('#skF_13', A_2307)) | ~v1_relat_1(A_2307) | ~r1_tarski(A_2307, '#skF_12') | r1_tarski(k2_relat_1(A_2307), k2_relat_1(k5_relat_1('#skF_13', A_2307))))), inference(resolution, [status(thm)], [c_6, c_63616])).
% 34.70/25.04  tff(c_578, plain, (![D_217, B_218, A_219, E_220]: (r2_hidden(k4_tarski('#skF_6'(D_217, B_218, A_219, E_220, k5_relat_1(A_219, B_218)), E_220), B_218) | ~r2_hidden(k4_tarski(D_217, E_220), k5_relat_1(A_219, B_218)) | ~v1_relat_1(k5_relat_1(A_219, B_218)) | ~v1_relat_1(B_218) | ~v1_relat_1(A_219))), inference(cnfTransformation, [status(thm)], [f_58])).
% 34.70/25.04  tff(c_1316, plain, (![E_289, B_290, D_291, A_292]: (r2_hidden(E_289, k2_relat_1(B_290)) | ~r2_hidden(k4_tarski(D_291, E_289), k5_relat_1(A_292, B_290)) | ~v1_relat_1(k5_relat_1(A_292, B_290)) | ~v1_relat_1(B_290) | ~v1_relat_1(A_292))), inference(resolution, [status(thm)], [c_578, c_10])).
% 34.70/25.04  tff(c_1384, plain, (![C_295, B_296, A_297]: (r2_hidden(C_295, k2_relat_1(B_296)) | ~v1_relat_1(k5_relat_1(A_297, B_296)) | ~v1_relat_1(B_296) | ~v1_relat_1(A_297) | ~r2_hidden(C_295, k2_relat_1(k5_relat_1(A_297, B_296))))), inference(resolution, [status(thm)], [c_8, c_1316])).
% 34.70/25.04  tff(c_15988, plain, (![A_933, B_934, B_935]: (r2_hidden('#skF_1'(k2_relat_1(k5_relat_1(A_933, B_934)), B_935), k2_relat_1(B_934)) | ~v1_relat_1(k5_relat_1(A_933, B_934)) | ~v1_relat_1(B_934) | ~v1_relat_1(A_933) | r1_tarski(k2_relat_1(k5_relat_1(A_933, B_934)), B_935))), inference(resolution, [status(thm)], [c_6, c_1384])).
% 34.70/25.04  tff(c_16048, plain, (![A_936, B_937]: (~v1_relat_1(k5_relat_1(A_936, B_937)) | ~v1_relat_1(B_937) | ~v1_relat_1(A_936) | r1_tarski(k2_relat_1(k5_relat_1(A_936, B_937)), k2_relat_1(B_937)))), inference(resolution, [status(thm)], [c_15988, c_4])).
% 34.70/25.04  tff(c_192, plain, (![A_179, B_180]: (r2_hidden(k4_tarski('#skF_3'(A_179, B_180), '#skF_2'(A_179, B_180)), A_179) | r2_hidden('#skF_4'(A_179, B_180), B_180) | k2_relat_1(A_179)=B_180)), inference(cnfTransformation, [status(thm)], [f_40])).
% 34.70/25.04  tff(c_317, plain, (![A_188, B_189]: (r2_hidden('#skF_2'(A_188, B_189), k2_relat_1(A_188)) | r2_hidden('#skF_4'(A_188, B_189), B_189) | k2_relat_1(A_188)=B_189)), inference(resolution, [status(thm)], [c_192, c_10])).
% 34.70/25.04  tff(c_678, plain, (![A_229, B_230, B_231]: (r2_hidden('#skF_2'(A_229, B_230), B_231) | ~r1_tarski(k2_relat_1(A_229), B_231) | r2_hidden('#skF_4'(A_229, B_230), B_230) | k2_relat_1(A_229)=B_230)), inference(resolution, [status(thm)], [c_317, c_2])).
% 34.70/25.04  tff(c_16, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), B_7) | r2_hidden('#skF_4'(A_6, B_7), B_7) | k2_relat_1(A_6)=B_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 34.70/25.04  tff(c_710, plain, (![A_232, B_233]: (~r1_tarski(k2_relat_1(A_232), B_233) | r2_hidden('#skF_4'(A_232, B_233), B_233) | k2_relat_1(A_232)=B_233)), inference(resolution, [status(thm)], [c_678, c_16])).
% 34.70/25.04  tff(c_721, plain, (![A_232, B_233, B_2]: (r2_hidden('#skF_4'(A_232, B_233), B_2) | ~r1_tarski(B_233, B_2) | ~r1_tarski(k2_relat_1(A_232), B_233) | k2_relat_1(A_232)=B_233)), inference(resolution, [status(thm)], [c_710, c_2])).
% 34.70/25.04  tff(c_342, plain, (![A_190, B_191, D_192]: (r2_hidden(k4_tarski('#skF_3'(A_190, B_191), '#skF_2'(A_190, B_191)), A_190) | ~r2_hidden(k4_tarski(D_192, '#skF_4'(A_190, B_191)), A_190) | k2_relat_1(A_190)=B_191)), inference(cnfTransformation, [status(thm)], [f_40])).
% 34.70/25.04  tff(c_1118, plain, (![A_259, B_260]: (r2_hidden(k4_tarski('#skF_3'(A_259, B_260), '#skF_2'(A_259, B_260)), A_259) | k2_relat_1(A_259)=B_260 | ~r2_hidden('#skF_4'(A_259, B_260), k2_relat_1(A_259)))), inference(resolution, [status(thm)], [c_8, c_342])).
% 34.70/25.04  tff(c_1137, plain, (![A_261, B_262]: (r2_hidden('#skF_2'(A_261, B_262), k2_relat_1(A_261)) | k2_relat_1(A_261)=B_262 | ~r2_hidden('#skF_4'(A_261, B_262), k2_relat_1(A_261)))), inference(resolution, [status(thm)], [c_1118, c_10])).
% 34.70/25.04  tff(c_1165, plain, (![A_268, B_269, B_270]: (r2_hidden('#skF_2'(A_268, B_269), B_270) | ~r1_tarski(k2_relat_1(A_268), B_270) | k2_relat_1(A_268)=B_269 | ~r2_hidden('#skF_4'(A_268, B_269), k2_relat_1(A_268)))), inference(resolution, [status(thm)], [c_1137, c_2])).
% 34.70/25.04  tff(c_3317, plain, (![A_435, B_436, B_437]: (r2_hidden('#skF_2'(A_435, B_436), B_437) | ~r1_tarski(k2_relat_1(A_435), B_437) | ~r1_tarski(B_436, k2_relat_1(A_435)) | ~r1_tarski(k2_relat_1(A_435), B_436) | k2_relat_1(A_435)=B_436)), inference(resolution, [status(thm)], [c_721, c_1165])).
% 34.70/25.04  tff(c_12, plain, (![A_6, B_7, D_20]: (~r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden(k4_tarski(D_20, '#skF_4'(A_6, B_7)), A_6) | k2_relat_1(A_6)=B_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 34.70/25.04  tff(c_3351, plain, (![D_438, A_439, B_440]: (~r2_hidden(k4_tarski(D_438, '#skF_4'(A_439, B_440)), A_439) | ~r1_tarski(B_440, k2_relat_1(A_439)) | ~r1_tarski(k2_relat_1(A_439), B_440) | k2_relat_1(A_439)=B_440)), inference(resolution, [status(thm)], [c_3317, c_12])).
% 34.70/25.04  tff(c_3434, plain, (![B_444, A_445]: (~r1_tarski(B_444, k2_relat_1(A_445)) | ~r1_tarski(k2_relat_1(A_445), B_444) | k2_relat_1(A_445)=B_444 | ~r2_hidden('#skF_4'(A_445, B_444), k2_relat_1(A_445)))), inference(resolution, [status(thm)], [c_8, c_3351])).
% 34.70/25.04  tff(c_3559, plain, (![B_233, A_232]: (~r1_tarski(B_233, k2_relat_1(A_232)) | ~r1_tarski(k2_relat_1(A_232), B_233) | k2_relat_1(A_232)=B_233)), inference(resolution, [status(thm)], [c_721, c_3434])).
% 34.70/25.04  tff(c_16188, plain, (![B_937, A_936]: (~r1_tarski(k2_relat_1(B_937), k2_relat_1(k5_relat_1(A_936, B_937))) | k2_relat_1(k5_relat_1(A_936, B_937))=k2_relat_1(B_937) | ~v1_relat_1(k5_relat_1(A_936, B_937)) | ~v1_relat_1(B_937) | ~v1_relat_1(A_936))), inference(resolution, [status(thm)], [c_16048, c_3559])).
% 34.70/25.04  tff(c_64061, plain, (![A_2307]: (k2_relat_1(k5_relat_1('#skF_13', A_2307))=k2_relat_1(A_2307) | ~v1_relat_1('#skF_13') | ~v1_relat_1(k5_relat_1('#skF_13', A_2307)) | ~v1_relat_1(A_2307) | ~r1_tarski(A_2307, '#skF_12'))), inference(resolution, [status(thm)], [c_63805, c_16188])).
% 34.70/25.04  tff(c_64354, plain, (![A_2308]: (k2_relat_1(k5_relat_1('#skF_13', A_2308))=k2_relat_1(A_2308) | ~v1_relat_1(k5_relat_1('#skF_13', A_2308)) | ~v1_relat_1(A_2308) | ~r1_tarski(A_2308, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_64061])).
% 34.70/25.04  tff(c_64358, plain, (![B_125]: (k2_relat_1(k5_relat_1('#skF_13', B_125))=k2_relat_1(B_125) | ~r1_tarski(B_125, '#skF_12') | ~v1_relat_1(B_125) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_38, c_64354])).
% 34.70/25.04  tff(c_64362, plain, (![B_2309]: (k2_relat_1(k5_relat_1('#skF_13', B_2309))=k2_relat_1(B_2309) | ~r1_tarski(B_2309, '#skF_12') | ~v1_relat_1(B_2309))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_64358])).
% 34.70/25.04  tff(c_44, plain, (k2_relat_1(k5_relat_1('#skF_13', '#skF_12'))!=k2_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_82])).
% 34.70/25.04  tff(c_65653, plain, (~r1_tarski('#skF_12', '#skF_12') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_64362, c_44])).
% 34.70/25.04  tff(c_65748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_57, c_65653])).
% 34.70/25.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.70/25.04  
% 34.70/25.04  Inference rules
% 34.70/25.04  ----------------------
% 34.70/25.04  #Ref     : 0
% 34.70/25.04  #Sup     : 15792
% 34.70/25.04  #Fact    : 10
% 34.70/25.04  #Define  : 0
% 34.70/25.04  #Split   : 33
% 34.70/25.04  #Chain   : 0
% 34.70/25.04  #Close   : 0
% 34.70/25.04  
% 34.70/25.04  Ordering : KBO
% 34.70/25.04  
% 34.70/25.04  Simplification rules
% 34.70/25.04  ----------------------
% 34.70/25.04  #Subsume      : 5479
% 34.70/25.04  #Demod        : 2710
% 34.70/25.04  #Tautology    : 575
% 34.70/25.04  #SimpNegUnit  : 0
% 34.70/25.04  #BackRed      : 18
% 34.70/25.04  
% 34.70/25.04  #Partial instantiations: 0
% 34.70/25.04  #Strategies tried      : 1
% 34.70/25.04  
% 34.70/25.04  Timing (in seconds)
% 34.70/25.04  ----------------------
% 34.70/25.04  Preprocessing        : 0.33
% 34.70/25.04  Parsing              : 0.16
% 34.70/25.04  CNF conversion       : 0.04
% 34.70/25.04  Main loop            : 23.95
% 34.70/25.04  Inferencing          : 3.00
% 34.70/25.04  Reduction            : 2.99
% 34.70/25.04  Demodulation         : 1.80
% 34.70/25.04  BG Simplification    : 0.27
% 34.70/25.04  Subsumption          : 16.68
% 34.70/25.04  Abstraction          : 0.51
% 34.70/25.04  MUC search           : 0.00
% 34.70/25.04  Cooper               : 0.00
% 34.70/25.04  Total                : 24.32
% 34.70/25.04  Index Insertion      : 0.00
% 34.70/25.04  Index Deletion       : 0.00
% 34.70/25.04  Index Matching       : 0.00
% 34.70/25.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
