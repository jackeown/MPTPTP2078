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
% DateTime   : Thu Dec  3 10:02:57 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :  111 (1234 expanded)
%              Number of leaves         :   35 ( 444 expanded)
%              Depth                    :   37
%              Number of atoms          :  293 (3938 expanded)
%              Number of equality atoms :  169 (2688 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( H = k5_enumset1(A,B,C,D,E,F,G)
    <=> ! [I] :
          ( r2_hidden(I,H)
        <=> ~ ( I != A
              & I != B
              & I != C
              & I != D
              & I != E
              & I != F
              & I != G ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_86,plain,(
    k1_tarski('#skF_7') = k1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_148,plain,(
    ! [F_148,B_149,D_152,C_153,E_150,A_151] : k5_enumset1(A_151,A_151,B_149,C_153,D_152,E_150,F_148) = k4_enumset1(A_151,B_149,C_153,D_152,E_150,F_148) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [G_35,A_29,I_39,F_34,D_32,C_31,B_30] : r2_hidden(I_39,k5_enumset1(A_29,B_30,C_31,D_32,I_39,F_34,G_35)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_178,plain,(
    ! [C_158,A_156,B_159,D_157,F_155,E_154] : r2_hidden(D_157,k4_enumset1(A_156,B_159,C_158,D_157,E_154,F_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_22])).

tff(c_194,plain,(
    ! [A_163,E_166,C_162,D_165,B_164] : r2_hidden(C_162,k3_enumset1(A_163,B_164,C_162,D_165,E_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_178])).

tff(c_198,plain,(
    ! [B_167,A_168,C_169,D_170] : r2_hidden(B_167,k2_enumset1(A_168,B_167,C_169,D_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_194])).

tff(c_202,plain,(
    ! [A_171,B_172,C_173] : r2_hidden(A_171,k1_enumset1(A_171,B_172,C_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_198])).

tff(c_206,plain,(
    ! [A_174,B_175] : r2_hidden(A_174,k2_tarski(A_174,B_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_202])).

tff(c_210,plain,(
    ! [A_176] : r2_hidden(A_176,k1_tarski(A_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_206])).

tff(c_213,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_210])).

tff(c_84,plain,(
    k1_tarski(k1_funct_1('#skF_8','#skF_7')) != k2_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_90,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_88,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_209,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_206])).

tff(c_78,plain,(
    ! [A_40,B_62] :
      ( k1_funct_1(A_40,'#skF_4'(A_40,B_62)) = '#skF_3'(A_40,B_62)
      | r2_hidden('#skF_5'(A_40,B_62),B_62)
      | k2_relat_1(A_40) = B_62
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_310,plain,(
    ! [D_268,F_272,B_270,A_271,I_275,C_274,G_269,E_273] :
      ( I_275 = G_269
      | I_275 = F_272
      | I_275 = E_273
      | I_275 = D_268
      | I_275 = C_274
      | I_275 = B_270
      | I_275 = A_271
      | ~ r2_hidden(I_275,k5_enumset1(A_271,B_270,C_274,D_268,E_273,F_272,G_269)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_359,plain,(
    ! [B_278,F_276,C_282,A_280,D_281,E_279,I_277] :
      ( I_277 = F_276
      | I_277 = E_279
      | I_277 = D_281
      | I_277 = C_282
      | I_277 = B_278
      | I_277 = A_280
      | I_277 = A_280
      | ~ r2_hidden(I_277,k4_enumset1(A_280,B_278,C_282,D_281,E_279,F_276)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_310])).

tff(c_403,plain,(
    ! [A_285,B_286,D_287,E_288,I_284,C_283] :
      ( I_284 = E_288
      | I_284 = D_287
      | I_284 = C_283
      | I_284 = B_286
      | I_284 = A_285
      | I_284 = A_285
      | I_284 = A_285
      | ~ r2_hidden(I_284,k3_enumset1(A_285,B_286,C_283,D_287,E_288)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_359])).

tff(c_442,plain,(
    ! [I_293,D_289,B_290,C_291,A_292] :
      ( I_293 = D_289
      | I_293 = C_291
      | I_293 = B_290
      | I_293 = A_292
      | I_293 = A_292
      | I_293 = A_292
      | I_293 = A_292
      | ~ r2_hidden(I_293,k2_enumset1(A_292,B_290,C_291,D_289)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_403])).

tff(c_476,plain,(
    ! [I_294,C_295,B_296,A_297] :
      ( I_294 = C_295
      | I_294 = B_296
      | I_294 = A_297
      | I_294 = A_297
      | I_294 = A_297
      | I_294 = A_297
      | I_294 = A_297
      | ~ r2_hidden(I_294,k1_enumset1(A_297,B_296,C_295)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_442])).

tff(c_505,plain,(
    ! [I_298,B_299,A_300] :
      ( I_298 = B_299
      | I_298 = A_300
      | I_298 = A_300
      | I_298 = A_300
      | I_298 = A_300
      | I_298 = A_300
      | I_298 = A_300
      | ~ r2_hidden(I_298,k2_tarski(A_300,B_299)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_476])).

tff(c_534,plain,(
    ! [I_304,A_305] :
      ( I_304 = A_305
      | I_304 = A_305
      | I_304 = A_305
      | I_304 = A_305
      | I_304 = A_305
      | I_304 = A_305
      | I_304 = A_305
      | ~ r2_hidden(I_304,k1_tarski(A_305)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_505])).

tff(c_1357,plain,(
    ! [A_370,A_371] :
      ( '#skF_5'(A_370,k1_tarski(A_371)) = A_371
      | k1_funct_1(A_370,'#skF_4'(A_370,k1_tarski(A_371))) = '#skF_3'(A_370,k1_tarski(A_371))
      | k2_relat_1(A_370) = k1_tarski(A_371)
      | ~ v1_funct_1(A_370)
      | ~ v1_relat_1(A_370) ) ),
    inference(resolution,[status(thm)],[c_78,c_534])).

tff(c_80,plain,(
    ! [A_40,B_62] :
      ( r2_hidden('#skF_4'(A_40,B_62),k1_relat_1(A_40))
      | r2_hidden('#skF_5'(A_40,B_62),B_62)
      | k2_relat_1(A_40) = B_62
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_82,plain,(
    ! [B_81,A_80] :
      ( r2_hidden(k1_funct_1(B_81,A_80),k2_relat_1(B_81))
      | ~ r2_hidden(A_80,k1_relat_1(B_81))
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_68,plain,(
    ! [A_40,C_76] :
      ( r2_hidden('#skF_6'(A_40,k2_relat_1(A_40),C_76),k1_relat_1(A_40))
      | ~ r2_hidden(C_76,k2_relat_1(A_40))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_553,plain,(
    ! [I_306] :
      ( I_306 = '#skF_7'
      | I_306 = '#skF_7'
      | I_306 = '#skF_7'
      | I_306 = '#skF_7'
      | I_306 = '#skF_7'
      | I_306 = '#skF_7'
      | I_306 = '#skF_7'
      | ~ r2_hidden(I_306,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_534])).

tff(c_572,plain,(
    ! [C_76] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),C_76) = '#skF_7'
      | ~ r2_hidden(C_76,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_68,c_553])).

tff(c_583,plain,(
    ! [C_307] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),C_307) = '#skF_7'
      | ~ r2_hidden(C_307,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_572])).

tff(c_595,plain,(
    ! [A_80] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),k1_funct_1('#skF_8',A_80)) = '#skF_7'
      | ~ r2_hidden(A_80,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_82,c_583])).

tff(c_656,plain,(
    ! [A_310] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),k1_funct_1('#skF_8',A_310)) = '#skF_7'
      | ~ r2_hidden(A_310,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_595])).

tff(c_66,plain,(
    ! [A_40,C_76] :
      ( k1_funct_1(A_40,'#skF_6'(A_40,k2_relat_1(A_40),C_76)) = C_76
      | ~ r2_hidden(C_76,k2_relat_1(A_40))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_665,plain,(
    ! [A_310] :
      ( k1_funct_1('#skF_8',A_310) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_8',A_310),k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(A_310,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_66])).

tff(c_865,plain,(
    ! [A_331] :
      ( k1_funct_1('#skF_8',A_331) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_8',A_331),k2_relat_1('#skF_8'))
      | ~ r2_hidden(A_331,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_665])).

tff(c_875,plain,(
    ! [A_80] :
      ( k1_funct_1('#skF_8',A_80) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(A_80,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_82,c_865])).

tff(c_881,plain,(
    ! [A_332] :
      ( k1_funct_1('#skF_8',A_332) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(A_332,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_875])).

tff(c_897,plain,(
    ! [B_62] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',B_62)) = k1_funct_1('#skF_8','#skF_7')
      | r2_hidden('#skF_5'('#skF_8',B_62),B_62)
      | k2_relat_1('#skF_8') = B_62
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_80,c_881])).

tff(c_1102,plain,(
    ! [B_345] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',B_345)) = k1_funct_1('#skF_8','#skF_7')
      | r2_hidden('#skF_5'('#skF_8',B_345),B_345)
      | k2_relat_1('#skF_8') = B_345 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_897])).

tff(c_522,plain,(
    ! [I_298,A_1] :
      ( I_298 = A_1
      | I_298 = A_1
      | I_298 = A_1
      | I_298 = A_1
      | I_298 = A_1
      | I_298 = A_1
      | I_298 = A_1
      | ~ r2_hidden(I_298,k1_tarski(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_505])).

tff(c_1163,plain,(
    ! [A_1] :
      ( '#skF_5'('#skF_8',k1_tarski(A_1)) = A_1
      | k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(A_1))) = k1_funct_1('#skF_8','#skF_7')
      | k2_relat_1('#skF_8') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_1102,c_522])).

tff(c_1364,plain,(
    ! [A_371] :
      ( '#skF_5'('#skF_8',k1_tarski(A_371)) = A_371
      | '#skF_3'('#skF_8',k1_tarski(A_371)) = k1_funct_1('#skF_8','#skF_7')
      | k2_relat_1('#skF_8') = k1_tarski(A_371)
      | '#skF_5'('#skF_8',k1_tarski(A_371)) = A_371
      | k2_relat_1('#skF_8') = k1_tarski(A_371)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1357,c_1163])).

tff(c_1404,plain,(
    ! [A_372] :
      ( '#skF_3'('#skF_8',k1_tarski(A_372)) = k1_funct_1('#skF_8','#skF_7')
      | '#skF_5'('#skF_8',k1_tarski(A_372)) = A_372
      | k2_relat_1('#skF_8') = k1_tarski(A_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_1364])).

tff(c_76,plain,(
    ! [A_40,B_62] :
      ( ~ r2_hidden('#skF_3'(A_40,B_62),B_62)
      | r2_hidden('#skF_5'(A_40,B_62),B_62)
      | k2_relat_1(A_40) = B_62
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1412,plain,(
    ! [A_372] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(A_372))
      | r2_hidden('#skF_5'('#skF_8',k1_tarski(A_372)),k1_tarski(A_372))
      | k2_relat_1('#skF_8') = k1_tarski(A_372)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | '#skF_5'('#skF_8',k1_tarski(A_372)) = A_372
      | k2_relat_1('#skF_8') = k1_tarski(A_372) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_76])).

tff(c_1450,plain,(
    ! [A_375] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(A_375))
      | r2_hidden('#skF_5'('#skF_8',k1_tarski(A_375)),k1_tarski(A_375))
      | '#skF_5'('#skF_8',k1_tarski(A_375)) = A_375
      | k2_relat_1('#skF_8') = k1_tarski(A_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_1412])).

tff(c_1469,plain,(
    ! [A_376] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(A_376))
      | '#skF_5'('#skF_8',k1_tarski(A_376)) = A_376
      | k2_relat_1('#skF_8') = k1_tarski(A_376) ) ),
    inference(resolution,[status(thm)],[c_1450,c_522])).

tff(c_1473,plain,
    ( '#skF_5'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7')
    | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_209,c_1469])).

tff(c_1479,plain,(
    '#skF_5'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1473])).

tff(c_74,plain,(
    ! [A_40,B_62,D_75] :
      ( r2_hidden('#skF_4'(A_40,B_62),k1_relat_1(A_40))
      | k1_funct_1(A_40,D_75) != '#skF_5'(A_40,B_62)
      | ~ r2_hidden(D_75,k1_relat_1(A_40))
      | k2_relat_1(A_40) = B_62
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1495,plain,(
    ! [D_75] :
      ( r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',D_75) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_75,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1479,c_74])).

tff(c_1517,plain,(
    ! [D_75] :
      ( r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',D_75) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_75,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_1495])).

tff(c_1518,plain,(
    ! [D_75] :
      ( r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',D_75) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_75,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1517])).

tff(c_1530,plain,(
    ! [D_385] :
      ( k1_funct_1('#skF_8',D_385) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_385,k1_relat_1('#skF_8')) ) ),
    inference(splitLeft,[status(thm)],[c_1518])).

tff(c_1603,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_213,c_1530])).

tff(c_1604,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1518])).

tff(c_548,plain,(
    ! [I_304] :
      ( I_304 = '#skF_7'
      | I_304 = '#skF_7'
      | I_304 = '#skF_7'
      | I_304 = '#skF_7'
      | I_304 = '#skF_7'
      | I_304 = '#skF_7'
      | I_304 = '#skF_7'
      | ~ r2_hidden(I_304,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_534])).

tff(c_1612,plain,(
    '#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1604,c_548])).

tff(c_72,plain,(
    ! [A_40,B_62,D_75] :
      ( k1_funct_1(A_40,'#skF_4'(A_40,B_62)) = '#skF_3'(A_40,B_62)
      | k1_funct_1(A_40,D_75) != '#skF_5'(A_40,B_62)
      | ~ r2_hidden(D_75,k1_relat_1(A_40))
      | k2_relat_1(A_40) = B_62
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1493,plain,(
    ! [D_75] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))) = '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_75) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_75,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1479,c_72])).

tff(c_1514,plain,(
    ! [D_75] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))) = '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_75) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_75,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_1493])).

tff(c_1515,plain,(
    ! [D_75] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))) = '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_75) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_75,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1514])).

tff(c_1645,plain,(
    ! [D_75] :
      ( '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7')
      | k1_funct_1('#skF_8',D_75) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_75,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_1515])).

tff(c_1647,plain,(
    ! [D_386] :
      ( k1_funct_1('#skF_8',D_386) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_386,k1_relat_1('#skF_8')) ) ),
    inference(splitLeft,[status(thm)],[c_1645])).

tff(c_1720,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_213,c_1647])).

tff(c_1721,plain,(
    '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1645])).

tff(c_70,plain,(
    ! [A_40,B_62,D_75] :
      ( ~ r2_hidden('#skF_3'(A_40,B_62),B_62)
      | k1_funct_1(A_40,D_75) != '#skF_5'(A_40,B_62)
      | ~ r2_hidden(D_75,k1_relat_1(A_40))
      | k2_relat_1(A_40) = B_62
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1727,plain,(
    ! [D_75] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_75) != '#skF_5'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_75,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1721,c_70])).

tff(c_1740,plain,(
    ! [D_75] :
      ( k1_funct_1('#skF_8',D_75) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_75,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_1479,c_209,c_1727])).

tff(c_1749,plain,(
    ! [D_387] :
      ( k1_funct_1('#skF_8',D_387) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_387,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1740])).

tff(c_1822,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_213,c_1749])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:25:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.91  
% 4.53/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.91  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 4.53/1.91  
% 4.53/1.91  %Foreground sorts:
% 4.53/1.91  
% 4.53/1.91  
% 4.53/1.91  %Background operators:
% 4.53/1.91  
% 4.53/1.91  
% 4.53/1.91  %Foreground operators:
% 4.53/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.53/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.91  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.53/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.91  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.53/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.53/1.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.53/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.53/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.53/1.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.53/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.53/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.53/1.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.53/1.91  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.53/1.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.53/1.91  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.53/1.91  tff('#skF_8', type, '#skF_8': $i).
% 4.53/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.53/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.53/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.91  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.53/1.91  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.53/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.53/1.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.53/1.91  
% 4.88/1.93  tff(f_98, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.88/1.93  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.88/1.93  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.88/1.93  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.88/1.93  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.88/1.93  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.88/1.93  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.88/1.93  tff(f_66, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_enumset1)).
% 4.88/1.93  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.88/1.93  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 4.88/1.93  tff(c_86, plain, (k1_tarski('#skF_7')=k1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.88/1.93  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.88/1.93  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.88/1.93  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.88/1.93  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.88/1.93  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.88/1.93  tff(c_148, plain, (![F_148, B_149, D_152, C_153, E_150, A_151]: (k5_enumset1(A_151, A_151, B_149, C_153, D_152, E_150, F_148)=k4_enumset1(A_151, B_149, C_153, D_152, E_150, F_148))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.88/1.93  tff(c_22, plain, (![G_35, A_29, I_39, F_34, D_32, C_31, B_30]: (r2_hidden(I_39, k5_enumset1(A_29, B_30, C_31, D_32, I_39, F_34, G_35)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.88/1.93  tff(c_178, plain, (![C_158, A_156, B_159, D_157, F_155, E_154]: (r2_hidden(D_157, k4_enumset1(A_156, B_159, C_158, D_157, E_154, F_155)))), inference(superposition, [status(thm), theory('equality')], [c_148, c_22])).
% 4.88/1.93  tff(c_194, plain, (![A_163, E_166, C_162, D_165, B_164]: (r2_hidden(C_162, k3_enumset1(A_163, B_164, C_162, D_165, E_166)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_178])).
% 4.88/1.93  tff(c_198, plain, (![B_167, A_168, C_169, D_170]: (r2_hidden(B_167, k2_enumset1(A_168, B_167, C_169, D_170)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_194])).
% 4.88/1.93  tff(c_202, plain, (![A_171, B_172, C_173]: (r2_hidden(A_171, k1_enumset1(A_171, B_172, C_173)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_198])).
% 4.88/1.93  tff(c_206, plain, (![A_174, B_175]: (r2_hidden(A_174, k2_tarski(A_174, B_175)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_202])).
% 4.88/1.93  tff(c_210, plain, (![A_176]: (r2_hidden(A_176, k1_tarski(A_176)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_206])).
% 4.88/1.93  tff(c_213, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_210])).
% 4.88/1.93  tff(c_84, plain, (k1_tarski(k1_funct_1('#skF_8', '#skF_7'))!=k2_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.88/1.93  tff(c_90, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.88/1.93  tff(c_88, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.88/1.93  tff(c_209, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_206])).
% 4.88/1.93  tff(c_78, plain, (![A_40, B_62]: (k1_funct_1(A_40, '#skF_4'(A_40, B_62))='#skF_3'(A_40, B_62) | r2_hidden('#skF_5'(A_40, B_62), B_62) | k2_relat_1(A_40)=B_62 | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.88/1.93  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.88/1.93  tff(c_310, plain, (![D_268, F_272, B_270, A_271, I_275, C_274, G_269, E_273]: (I_275=G_269 | I_275=F_272 | I_275=E_273 | I_275=D_268 | I_275=C_274 | I_275=B_270 | I_275=A_271 | ~r2_hidden(I_275, k5_enumset1(A_271, B_270, C_274, D_268, E_273, F_272, G_269)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.88/1.93  tff(c_359, plain, (![B_278, F_276, C_282, A_280, D_281, E_279, I_277]: (I_277=F_276 | I_277=E_279 | I_277=D_281 | I_277=C_282 | I_277=B_278 | I_277=A_280 | I_277=A_280 | ~r2_hidden(I_277, k4_enumset1(A_280, B_278, C_282, D_281, E_279, F_276)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_310])).
% 4.88/1.93  tff(c_403, plain, (![A_285, B_286, D_287, E_288, I_284, C_283]: (I_284=E_288 | I_284=D_287 | I_284=C_283 | I_284=B_286 | I_284=A_285 | I_284=A_285 | I_284=A_285 | ~r2_hidden(I_284, k3_enumset1(A_285, B_286, C_283, D_287, E_288)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_359])).
% 4.88/1.93  tff(c_442, plain, (![I_293, D_289, B_290, C_291, A_292]: (I_293=D_289 | I_293=C_291 | I_293=B_290 | I_293=A_292 | I_293=A_292 | I_293=A_292 | I_293=A_292 | ~r2_hidden(I_293, k2_enumset1(A_292, B_290, C_291, D_289)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_403])).
% 4.88/1.93  tff(c_476, plain, (![I_294, C_295, B_296, A_297]: (I_294=C_295 | I_294=B_296 | I_294=A_297 | I_294=A_297 | I_294=A_297 | I_294=A_297 | I_294=A_297 | ~r2_hidden(I_294, k1_enumset1(A_297, B_296, C_295)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_442])).
% 4.88/1.93  tff(c_505, plain, (![I_298, B_299, A_300]: (I_298=B_299 | I_298=A_300 | I_298=A_300 | I_298=A_300 | I_298=A_300 | I_298=A_300 | I_298=A_300 | ~r2_hidden(I_298, k2_tarski(A_300, B_299)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_476])).
% 4.88/1.93  tff(c_534, plain, (![I_304, A_305]: (I_304=A_305 | I_304=A_305 | I_304=A_305 | I_304=A_305 | I_304=A_305 | I_304=A_305 | I_304=A_305 | ~r2_hidden(I_304, k1_tarski(A_305)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_505])).
% 4.88/1.93  tff(c_1357, plain, (![A_370, A_371]: ('#skF_5'(A_370, k1_tarski(A_371))=A_371 | k1_funct_1(A_370, '#skF_4'(A_370, k1_tarski(A_371)))='#skF_3'(A_370, k1_tarski(A_371)) | k2_relat_1(A_370)=k1_tarski(A_371) | ~v1_funct_1(A_370) | ~v1_relat_1(A_370))), inference(resolution, [status(thm)], [c_78, c_534])).
% 4.88/1.93  tff(c_80, plain, (![A_40, B_62]: (r2_hidden('#skF_4'(A_40, B_62), k1_relat_1(A_40)) | r2_hidden('#skF_5'(A_40, B_62), B_62) | k2_relat_1(A_40)=B_62 | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.88/1.93  tff(c_82, plain, (![B_81, A_80]: (r2_hidden(k1_funct_1(B_81, A_80), k2_relat_1(B_81)) | ~r2_hidden(A_80, k1_relat_1(B_81)) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.88/1.93  tff(c_68, plain, (![A_40, C_76]: (r2_hidden('#skF_6'(A_40, k2_relat_1(A_40), C_76), k1_relat_1(A_40)) | ~r2_hidden(C_76, k2_relat_1(A_40)) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.88/1.93  tff(c_553, plain, (![I_306]: (I_306='#skF_7' | I_306='#skF_7' | I_306='#skF_7' | I_306='#skF_7' | I_306='#skF_7' | I_306='#skF_7' | I_306='#skF_7' | ~r2_hidden(I_306, k1_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_86, c_534])).
% 4.88/1.93  tff(c_572, plain, (![C_76]: ('#skF_6'('#skF_8', k2_relat_1('#skF_8'), C_76)='#skF_7' | ~r2_hidden(C_76, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_68, c_553])).
% 4.88/1.93  tff(c_583, plain, (![C_307]: ('#skF_6'('#skF_8', k2_relat_1('#skF_8'), C_307)='#skF_7' | ~r2_hidden(C_307, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_572])).
% 4.88/1.93  tff(c_595, plain, (![A_80]: ('#skF_6'('#skF_8', k2_relat_1('#skF_8'), k1_funct_1('#skF_8', A_80))='#skF_7' | ~r2_hidden(A_80, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_82, c_583])).
% 4.88/1.93  tff(c_656, plain, (![A_310]: ('#skF_6'('#skF_8', k2_relat_1('#skF_8'), k1_funct_1('#skF_8', A_310))='#skF_7' | ~r2_hidden(A_310, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_595])).
% 4.88/1.93  tff(c_66, plain, (![A_40, C_76]: (k1_funct_1(A_40, '#skF_6'(A_40, k2_relat_1(A_40), C_76))=C_76 | ~r2_hidden(C_76, k2_relat_1(A_40)) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.88/1.93  tff(c_665, plain, (![A_310]: (k1_funct_1('#skF_8', A_310)=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(k1_funct_1('#skF_8', A_310), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(A_310, k1_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_656, c_66])).
% 4.88/1.93  tff(c_865, plain, (![A_331]: (k1_funct_1('#skF_8', A_331)=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(k1_funct_1('#skF_8', A_331), k2_relat_1('#skF_8')) | ~r2_hidden(A_331, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_665])).
% 4.88/1.93  tff(c_875, plain, (![A_80]: (k1_funct_1('#skF_8', A_80)=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(A_80, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_82, c_865])).
% 4.88/1.93  tff(c_881, plain, (![A_332]: (k1_funct_1('#skF_8', A_332)=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(A_332, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_875])).
% 4.88/1.93  tff(c_897, plain, (![B_62]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', B_62))=k1_funct_1('#skF_8', '#skF_7') | r2_hidden('#skF_5'('#skF_8', B_62), B_62) | k2_relat_1('#skF_8')=B_62 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_80, c_881])).
% 4.88/1.93  tff(c_1102, plain, (![B_345]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', B_345))=k1_funct_1('#skF_8', '#skF_7') | r2_hidden('#skF_5'('#skF_8', B_345), B_345) | k2_relat_1('#skF_8')=B_345)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_897])).
% 4.88/1.93  tff(c_522, plain, (![I_298, A_1]: (I_298=A_1 | I_298=A_1 | I_298=A_1 | I_298=A_1 | I_298=A_1 | I_298=A_1 | I_298=A_1 | ~r2_hidden(I_298, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_505])).
% 4.88/1.93  tff(c_1163, plain, (![A_1]: ('#skF_5'('#skF_8', k1_tarski(A_1))=A_1 | k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_tarski(A_1)))=k1_funct_1('#skF_8', '#skF_7') | k2_relat_1('#skF_8')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_1102, c_522])).
% 4.88/1.93  tff(c_1364, plain, (![A_371]: ('#skF_5'('#skF_8', k1_tarski(A_371))=A_371 | '#skF_3'('#skF_8', k1_tarski(A_371))=k1_funct_1('#skF_8', '#skF_7') | k2_relat_1('#skF_8')=k1_tarski(A_371) | '#skF_5'('#skF_8', k1_tarski(A_371))=A_371 | k2_relat_1('#skF_8')=k1_tarski(A_371) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1357, c_1163])).
% 4.88/1.93  tff(c_1404, plain, (![A_372]: ('#skF_3'('#skF_8', k1_tarski(A_372))=k1_funct_1('#skF_8', '#skF_7') | '#skF_5'('#skF_8', k1_tarski(A_372))=A_372 | k2_relat_1('#skF_8')=k1_tarski(A_372))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_1364])).
% 4.88/1.93  tff(c_76, plain, (![A_40, B_62]: (~r2_hidden('#skF_3'(A_40, B_62), B_62) | r2_hidden('#skF_5'(A_40, B_62), B_62) | k2_relat_1(A_40)=B_62 | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.88/1.93  tff(c_1412, plain, (![A_372]: (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski(A_372)) | r2_hidden('#skF_5'('#skF_8', k1_tarski(A_372)), k1_tarski(A_372)) | k2_relat_1('#skF_8')=k1_tarski(A_372) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_5'('#skF_8', k1_tarski(A_372))=A_372 | k2_relat_1('#skF_8')=k1_tarski(A_372))), inference(superposition, [status(thm), theory('equality')], [c_1404, c_76])).
% 4.88/1.93  tff(c_1450, plain, (![A_375]: (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski(A_375)) | r2_hidden('#skF_5'('#skF_8', k1_tarski(A_375)), k1_tarski(A_375)) | '#skF_5'('#skF_8', k1_tarski(A_375))=A_375 | k2_relat_1('#skF_8')=k1_tarski(A_375))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_1412])).
% 4.88/1.93  tff(c_1469, plain, (![A_376]: (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski(A_376)) | '#skF_5'('#skF_8', k1_tarski(A_376))=A_376 | k2_relat_1('#skF_8')=k1_tarski(A_376))), inference(resolution, [status(thm)], [c_1450, c_522])).
% 4.88/1.93  tff(c_1473, plain, ('#skF_5'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7')))=k1_funct_1('#skF_8', '#skF_7') | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_209, c_1469])).
% 4.88/1.93  tff(c_1479, plain, ('#skF_5'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7')))=k1_funct_1('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_84, c_1473])).
% 4.88/1.93  tff(c_74, plain, (![A_40, B_62, D_75]: (r2_hidden('#skF_4'(A_40, B_62), k1_relat_1(A_40)) | k1_funct_1(A_40, D_75)!='#skF_5'(A_40, B_62) | ~r2_hidden(D_75, k1_relat_1(A_40)) | k2_relat_1(A_40)=B_62 | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.88/1.93  tff(c_1495, plain, (![D_75]: (r2_hidden('#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', D_75)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_75, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1479, c_74])).
% 4.88/1.93  tff(c_1517, plain, (![D_75]: (r2_hidden('#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', D_75)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_75, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_1495])).
% 4.88/1.93  tff(c_1518, plain, (![D_75]: (r2_hidden('#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', D_75)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_75, k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_84, c_1517])).
% 4.88/1.93  tff(c_1530, plain, (![D_385]: (k1_funct_1('#skF_8', D_385)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_385, k1_relat_1('#skF_8')))), inference(splitLeft, [status(thm)], [c_1518])).
% 4.88/1.93  tff(c_1603, plain, $false, inference(resolution, [status(thm)], [c_213, c_1530])).
% 4.88/1.93  tff(c_1604, plain, (r2_hidden('#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_1518])).
% 4.88/1.93  tff(c_548, plain, (![I_304]: (I_304='#skF_7' | I_304='#skF_7' | I_304='#skF_7' | I_304='#skF_7' | I_304='#skF_7' | I_304='#skF_7' | I_304='#skF_7' | ~r2_hidden(I_304, k1_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_86, c_534])).
% 4.88/1.93  tff(c_1612, plain, ('#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7')))='#skF_7'), inference(resolution, [status(thm)], [c_1604, c_548])).
% 4.88/1.93  tff(c_72, plain, (![A_40, B_62, D_75]: (k1_funct_1(A_40, '#skF_4'(A_40, B_62))='#skF_3'(A_40, B_62) | k1_funct_1(A_40, D_75)!='#skF_5'(A_40, B_62) | ~r2_hidden(D_75, k1_relat_1(A_40)) | k2_relat_1(A_40)=B_62 | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.88/1.93  tff(c_1493, plain, (![D_75]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))))='#skF_3'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))) | k1_funct_1('#skF_8', D_75)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_75, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1479, c_72])).
% 4.88/1.93  tff(c_1514, plain, (![D_75]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))))='#skF_3'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))) | k1_funct_1('#skF_8', D_75)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_75, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_1493])).
% 4.88/1.93  tff(c_1515, plain, (![D_75]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))))='#skF_3'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))) | k1_funct_1('#skF_8', D_75)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_75, k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_84, c_1514])).
% 4.88/1.93  tff(c_1645, plain, (![D_75]: ('#skF_3'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7')))=k1_funct_1('#skF_8', '#skF_7') | k1_funct_1('#skF_8', D_75)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_75, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_1515])).
% 4.88/1.93  tff(c_1647, plain, (![D_386]: (k1_funct_1('#skF_8', D_386)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_386, k1_relat_1('#skF_8')))), inference(splitLeft, [status(thm)], [c_1645])).
% 4.88/1.93  tff(c_1720, plain, $false, inference(resolution, [status(thm)], [c_213, c_1647])).
% 4.88/1.93  tff(c_1721, plain, ('#skF_3'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7')))=k1_funct_1('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_1645])).
% 4.88/1.93  tff(c_70, plain, (![A_40, B_62, D_75]: (~r2_hidden('#skF_3'(A_40, B_62), B_62) | k1_funct_1(A_40, D_75)!='#skF_5'(A_40, B_62) | ~r2_hidden(D_75, k1_relat_1(A_40)) | k2_relat_1(A_40)=B_62 | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.88/1.93  tff(c_1727, plain, (![D_75]: (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski(k1_funct_1('#skF_8', '#skF_7'))) | k1_funct_1('#skF_8', D_75)!='#skF_5'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_75, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1721, c_70])).
% 4.88/1.93  tff(c_1740, plain, (![D_75]: (k1_funct_1('#skF_8', D_75)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_75, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_1479, c_209, c_1727])).
% 4.88/1.93  tff(c_1749, plain, (![D_387]: (k1_funct_1('#skF_8', D_387)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_387, k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_84, c_1740])).
% 4.88/1.93  tff(c_1822, plain, $false, inference(resolution, [status(thm)], [c_213, c_1749])).
% 4.88/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.93  
% 4.88/1.93  Inference rules
% 4.88/1.93  ----------------------
% 4.88/1.93  #Ref     : 0
% 4.88/1.93  #Sup     : 332
% 4.88/1.93  #Fact    : 0
% 4.88/1.93  #Define  : 0
% 4.88/1.93  #Split   : 8
% 4.88/1.93  #Chain   : 0
% 4.88/1.93  #Close   : 0
% 4.88/1.93  
% 4.88/1.93  Ordering : KBO
% 4.88/1.93  
% 4.88/1.93  Simplification rules
% 4.88/1.93  ----------------------
% 4.88/1.93  #Subsume      : 26
% 4.88/1.93  #Demod        : 352
% 4.88/1.93  #Tautology    : 171
% 4.88/1.93  #SimpNegUnit  : 60
% 4.88/1.93  #BackRed      : 7
% 4.88/1.93  
% 4.88/1.93  #Partial instantiations: 0
% 4.88/1.93  #Strategies tried      : 1
% 4.88/1.93  
% 4.88/1.93  Timing (in seconds)
% 4.88/1.93  ----------------------
% 4.88/1.93  Preprocessing        : 0.40
% 4.88/1.93  Parsing              : 0.19
% 4.88/1.93  CNF conversion       : 0.03
% 4.88/1.93  Main loop            : 0.68
% 4.88/1.93  Inferencing          : 0.22
% 4.88/1.93  Reduction            : 0.21
% 4.88/1.93  Demodulation         : 0.16
% 4.88/1.94  BG Simplification    : 0.04
% 4.88/1.94  Subsumption          : 0.18
% 4.88/1.94  Abstraction          : 0.05
% 4.88/1.94  MUC search           : 0.00
% 4.88/1.94  Cooper               : 0.00
% 4.88/1.94  Total                : 1.11
% 4.88/1.94  Index Insertion      : 0.00
% 4.88/1.94  Index Deletion       : 0.00
% 4.88/1.94  Index Matching       : 0.00
% 4.88/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
