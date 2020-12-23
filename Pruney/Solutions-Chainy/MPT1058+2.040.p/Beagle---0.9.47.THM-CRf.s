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
% DateTime   : Thu Dec  3 10:17:27 EST 2020

% Result     : Theorem 5.00s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 171 expanded)
%              Number of leaves         :   39 (  81 expanded)
%              Depth                    :   23
%              Number of atoms          :  159 ( 323 expanded)
%              Number of equality atoms :   31 (  78 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_62,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_64,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_54,plain,(
    ! [A_52] : v1_relat_1(k6_relat_1(A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    ! [A_52] : v1_funct_1(k6_relat_1(A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_39] : k2_relat_1(k6_relat_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [A_39] : k1_relat_1(k6_relat_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_141,plain,(
    ! [A_76] :
      ( k9_relat_1(A_76,k1_relat_1(A_76)) = k2_relat_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_150,plain,(
    ! [A_39] :
      ( k9_relat_1(k6_relat_1(A_39),A_39) = k2_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_141])).

tff(c_154,plain,(
    ! [A_39] : k9_relat_1(k6_relat_1(A_39),A_39) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_34,c_150])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,(
    ! [A_75] :
      ( k10_relat_1(A_75,k2_relat_1(A_75)) = k1_relat_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_136,plain,(
    ! [A_39] :
      ( k10_relat_1(k6_relat_1(A_39),A_39) = k1_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_127])).

tff(c_140,plain,(
    ! [A_39] : k10_relat_1(k6_relat_1(A_39),A_39) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32,c_136])).

tff(c_222,plain,(
    ! [D_95,A_96,B_97] :
      ( r2_hidden(D_95,k1_relat_1(A_96))
      | ~ r2_hidden(D_95,k10_relat_1(A_96,B_97))
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_782,plain,(
    ! [A_171,B_172,B_173] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_171,B_172),B_173),k1_relat_1(A_171))
      | ~ v1_funct_1(A_171)
      | ~ v1_relat_1(A_171)
      | r1_tarski(k10_relat_1(A_171,B_172),B_173) ) ),
    inference(resolution,[status(thm)],[c_6,c_222])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_825,plain,(
    ! [A_177,B_178] :
      ( ~ v1_funct_1(A_177)
      | ~ v1_relat_1(A_177)
      | r1_tarski(k10_relat_1(A_177,B_178),k1_relat_1(A_177)) ) ),
    inference(resolution,[status(thm)],[c_782,c_4])).

tff(c_857,plain,(
    ! [A_39,B_178] :
      ( ~ v1_funct_1(k6_relat_1(A_39))
      | ~ v1_relat_1(k6_relat_1(A_39))
      | r1_tarski(k10_relat_1(k6_relat_1(A_39),B_178),A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_825])).

tff(c_870,plain,(
    ! [A_179,B_180] : r1_tarski(k10_relat_1(k6_relat_1(A_179),B_180),A_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_857])).

tff(c_265,plain,(
    ! [A_105,D_106,B_107] :
      ( r2_hidden(k1_funct_1(A_105,D_106),B_107)
      | ~ r2_hidden(D_106,k10_relat_1(A_105,B_107))
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_273,plain,(
    ! [A_105,D_106,B_2,B_107] :
      ( r2_hidden(k1_funct_1(A_105,D_106),B_2)
      | ~ r1_tarski(B_107,B_2)
      | ~ r2_hidden(D_106,k10_relat_1(A_105,B_107))
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(resolution,[status(thm)],[c_265,c_2])).

tff(c_1631,plain,(
    ! [A_244,D_245,A_246,B_247] :
      ( r2_hidden(k1_funct_1(A_244,D_245),A_246)
      | ~ r2_hidden(D_245,k10_relat_1(A_244,k10_relat_1(k6_relat_1(A_246),B_247)))
      | ~ v1_funct_1(A_244)
      | ~ v1_relat_1(A_244) ) ),
    inference(resolution,[status(thm)],[c_870,c_273])).

tff(c_1698,plain,(
    ! [A_246,B_247,D_245] :
      ( r2_hidden(k1_funct_1(k6_relat_1(k10_relat_1(k6_relat_1(A_246),B_247)),D_245),A_246)
      | ~ r2_hidden(D_245,k10_relat_1(k6_relat_1(A_246),B_247))
      | ~ v1_funct_1(k6_relat_1(k10_relat_1(k6_relat_1(A_246),B_247)))
      | ~ v1_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(A_246),B_247))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_1631])).

tff(c_1727,plain,(
    ! [A_248,B_249,D_250] :
      ( r2_hidden(k1_funct_1(k6_relat_1(k10_relat_1(k6_relat_1(A_248),B_249)),D_250),A_248)
      | ~ r2_hidden(D_250,k10_relat_1(k6_relat_1(A_248),B_249)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_1698])).

tff(c_1755,plain,(
    ! [A_39,D_250] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_39),D_250),A_39)
      | ~ r2_hidden(D_250,k10_relat_1(k6_relat_1(A_39),A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_1727])).

tff(c_1816,plain,(
    ! [A_254,D_255] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_254),D_255),A_254)
      | ~ r2_hidden(D_255,A_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1755])).

tff(c_1858,plain,(
    ! [A_256,D_257,B_258] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_256),D_257),B_258)
      | ~ r1_tarski(A_256,B_258)
      | ~ r2_hidden(D_257,A_256) ) ),
    inference(resolution,[status(thm)],[c_1816,c_2])).

tff(c_36,plain,(
    ! [D_51,A_40,B_47] :
      ( r2_hidden(D_51,k10_relat_1(A_40,B_47))
      | ~ r2_hidden(k1_funct_1(A_40,D_51),B_47)
      | ~ r2_hidden(D_51,k1_relat_1(A_40))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1881,plain,(
    ! [D_257,A_256,B_258] :
      ( r2_hidden(D_257,k10_relat_1(k6_relat_1(A_256),B_258))
      | ~ r2_hidden(D_257,k1_relat_1(k6_relat_1(A_256)))
      | ~ v1_funct_1(k6_relat_1(A_256))
      | ~ v1_relat_1(k6_relat_1(A_256))
      | ~ r1_tarski(A_256,B_258)
      | ~ r2_hidden(D_257,A_256) ) ),
    inference(resolution,[status(thm)],[c_1858,c_36])).

tff(c_1908,plain,(
    ! [D_262,A_263,B_264] :
      ( r2_hidden(D_262,k10_relat_1(k6_relat_1(A_263),B_264))
      | ~ r1_tarski(A_263,B_264)
      | ~ r2_hidden(D_262,A_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_32,c_1881])).

tff(c_2760,plain,(
    ! [A_319,A_320,B_321] :
      ( r1_tarski(A_319,k10_relat_1(k6_relat_1(A_320),B_321))
      | ~ r1_tarski(A_320,B_321)
      | ~ r2_hidden('#skF_1'(A_319,k10_relat_1(k6_relat_1(A_320),B_321)),A_320) ) ),
    inference(resolution,[status(thm)],[c_1908,c_4])).

tff(c_2842,plain,(
    ! [A_322,B_323] :
      ( ~ r1_tarski(A_322,B_323)
      | r1_tarski(A_322,k10_relat_1(k6_relat_1(A_322),B_323)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2760])).

tff(c_809,plain,(
    ! [A_39,B_172,B_173] :
      ( r2_hidden('#skF_1'(k10_relat_1(k6_relat_1(A_39),B_172),B_173),A_39)
      | ~ v1_funct_1(k6_relat_1(A_39))
      | ~ v1_relat_1(k6_relat_1(A_39))
      | r1_tarski(k10_relat_1(k6_relat_1(A_39),B_172),B_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_782])).

tff(c_1007,plain,(
    ! [A_189,B_190,B_191] :
      ( r2_hidden('#skF_1'(k10_relat_1(k6_relat_1(A_189),B_190),B_191),A_189)
      | r1_tarski(k10_relat_1(k6_relat_1(A_189),B_190),B_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_809])).

tff(c_1397,plain,(
    ! [A_221,B_222,B_223,B_224] :
      ( r2_hidden('#skF_1'(k10_relat_1(k6_relat_1(A_221),B_222),B_223),B_224)
      | ~ r1_tarski(A_221,B_224)
      | r1_tarski(k10_relat_1(k6_relat_1(A_221),B_222),B_223) ) ),
    inference(resolution,[status(thm)],[c_1007,c_2])).

tff(c_1436,plain,(
    ! [A_225,B_226,B_227] :
      ( ~ r1_tarski(A_225,B_226)
      | r1_tarski(k10_relat_1(k6_relat_1(A_225),B_227),B_226) ) ),
    inference(resolution,[status(thm)],[c_1397,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1482,plain,(
    ! [A_225,B_227,B_226] :
      ( k10_relat_1(k6_relat_1(A_225),B_227) = B_226
      | ~ r1_tarski(B_226,k10_relat_1(k6_relat_1(A_225),B_227))
      | ~ r1_tarski(A_225,B_226) ) ),
    inference(resolution,[status(thm)],[c_1436,c_8])).

tff(c_2861,plain,(
    ! [A_322,B_323] :
      ( k10_relat_1(k6_relat_1(A_322),B_323) = A_322
      | ~ r1_tarski(A_322,A_322)
      | ~ r1_tarski(A_322,B_323) ) ),
    inference(resolution,[status(thm)],[c_2842,c_1482])).

tff(c_3043,plain,(
    ! [A_328,B_329] :
      ( k10_relat_1(k6_relat_1(A_328),B_329) = A_328
      | ~ r1_tarski(A_328,B_329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2861])).

tff(c_28,plain,(
    ! [A_37] :
      ( k9_relat_1(A_37,k1_relat_1(A_37)) = k2_relat_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_326,plain,(
    ! [A_123,B_124] :
      ( k3_xboole_0(A_123,k9_relat_1(B_124,k1_relat_1(B_124))) = k9_relat_1(B_124,k10_relat_1(B_124,A_123))
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_335,plain,(
    ! [A_37,A_123] :
      ( k9_relat_1(A_37,k10_relat_1(A_37,A_123)) = k3_xboole_0(A_123,k2_relat_1(A_37))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_326])).

tff(c_3185,plain,(
    ! [A_328,B_329] :
      ( k9_relat_1(k6_relat_1(A_328),A_328) = k3_xboole_0(B_329,k2_relat_1(k6_relat_1(A_328)))
      | ~ v1_funct_1(k6_relat_1(A_328))
      | ~ v1_relat_1(k6_relat_1(A_328))
      | ~ v1_relat_1(k6_relat_1(A_328))
      | ~ r1_tarski(A_328,B_329) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3043,c_335])).

tff(c_3277,plain,(
    ! [B_330,A_331] :
      ( k3_xboole_0(B_330,A_331) = A_331
      | ~ r1_tarski(A_331,B_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_56,c_154,c_34,c_3185])).

tff(c_3312,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_3277])).

tff(c_58,plain,(
    ! [A_53,C_55,B_54] :
      ( k3_xboole_0(A_53,k10_relat_1(C_55,B_54)) = k10_relat_1(k7_relat_1(C_55,A_53),B_54)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3318,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3312,c_58])).

tff(c_3325,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3318])).

tff(c_3327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.00/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.95  
% 5.00/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.95  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.00/1.95  
% 5.00/1.95  %Foreground sorts:
% 5.00/1.95  
% 5.00/1.95  
% 5.00/1.95  %Background operators:
% 5.00/1.95  
% 5.00/1.95  
% 5.00/1.95  %Foreground operators:
% 5.00/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.00/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.00/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.00/1.95  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.00/1.95  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.00/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.00/1.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.00/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.00/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.00/1.95  tff('#skF_5', type, '#skF_5': $i).
% 5.00/1.95  tff('#skF_6', type, '#skF_6': $i).
% 5.00/1.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.00/1.95  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.00/1.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.00/1.95  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.00/1.95  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.00/1.95  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.00/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.00/1.95  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.00/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.00/1.95  tff('#skF_4', type, '#skF_4': $i).
% 5.00/1.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.00/1.95  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.00/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.00/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.00/1.95  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.00/1.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.00/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.00/1.95  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.00/1.95  
% 5.00/1.97  tff(f_102, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 5.00/1.97  tff(f_82, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.00/1.97  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.00/1.97  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 5.00/1.97  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.00/1.97  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.00/1.97  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 5.00/1.97  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 5.00/1.97  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 5.00/1.97  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 5.00/1.97  tff(c_62, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.00/1.97  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.00/1.97  tff(c_64, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.00/1.97  tff(c_54, plain, (![A_52]: (v1_relat_1(k6_relat_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.00/1.97  tff(c_56, plain, (![A_52]: (v1_funct_1(k6_relat_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.00/1.97  tff(c_34, plain, (![A_39]: (k2_relat_1(k6_relat_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.00/1.97  tff(c_32, plain, (![A_39]: (k1_relat_1(k6_relat_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.00/1.97  tff(c_141, plain, (![A_76]: (k9_relat_1(A_76, k1_relat_1(A_76))=k2_relat_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.00/1.97  tff(c_150, plain, (![A_39]: (k9_relat_1(k6_relat_1(A_39), A_39)=k2_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_141])).
% 5.00/1.97  tff(c_154, plain, (![A_39]: (k9_relat_1(k6_relat_1(A_39), A_39)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_34, c_150])).
% 5.00/1.97  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.00/1.97  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.00/1.97  tff(c_127, plain, (![A_75]: (k10_relat_1(A_75, k2_relat_1(A_75))=k1_relat_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.00/1.97  tff(c_136, plain, (![A_39]: (k10_relat_1(k6_relat_1(A_39), A_39)=k1_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_127])).
% 5.00/1.97  tff(c_140, plain, (![A_39]: (k10_relat_1(k6_relat_1(A_39), A_39)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_32, c_136])).
% 5.00/1.97  tff(c_222, plain, (![D_95, A_96, B_97]: (r2_hidden(D_95, k1_relat_1(A_96)) | ~r2_hidden(D_95, k10_relat_1(A_96, B_97)) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.00/1.97  tff(c_782, plain, (![A_171, B_172, B_173]: (r2_hidden('#skF_1'(k10_relat_1(A_171, B_172), B_173), k1_relat_1(A_171)) | ~v1_funct_1(A_171) | ~v1_relat_1(A_171) | r1_tarski(k10_relat_1(A_171, B_172), B_173))), inference(resolution, [status(thm)], [c_6, c_222])).
% 5.00/1.97  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.00/1.97  tff(c_825, plain, (![A_177, B_178]: (~v1_funct_1(A_177) | ~v1_relat_1(A_177) | r1_tarski(k10_relat_1(A_177, B_178), k1_relat_1(A_177)))), inference(resolution, [status(thm)], [c_782, c_4])).
% 5.00/1.97  tff(c_857, plain, (![A_39, B_178]: (~v1_funct_1(k6_relat_1(A_39)) | ~v1_relat_1(k6_relat_1(A_39)) | r1_tarski(k10_relat_1(k6_relat_1(A_39), B_178), A_39))), inference(superposition, [status(thm), theory('equality')], [c_32, c_825])).
% 5.00/1.97  tff(c_870, plain, (![A_179, B_180]: (r1_tarski(k10_relat_1(k6_relat_1(A_179), B_180), A_179))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_857])).
% 5.00/1.97  tff(c_265, plain, (![A_105, D_106, B_107]: (r2_hidden(k1_funct_1(A_105, D_106), B_107) | ~r2_hidden(D_106, k10_relat_1(A_105, B_107)) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.00/1.97  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.00/1.97  tff(c_273, plain, (![A_105, D_106, B_2, B_107]: (r2_hidden(k1_funct_1(A_105, D_106), B_2) | ~r1_tarski(B_107, B_2) | ~r2_hidden(D_106, k10_relat_1(A_105, B_107)) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(resolution, [status(thm)], [c_265, c_2])).
% 5.00/1.97  tff(c_1631, plain, (![A_244, D_245, A_246, B_247]: (r2_hidden(k1_funct_1(A_244, D_245), A_246) | ~r2_hidden(D_245, k10_relat_1(A_244, k10_relat_1(k6_relat_1(A_246), B_247))) | ~v1_funct_1(A_244) | ~v1_relat_1(A_244))), inference(resolution, [status(thm)], [c_870, c_273])).
% 5.00/1.97  tff(c_1698, plain, (![A_246, B_247, D_245]: (r2_hidden(k1_funct_1(k6_relat_1(k10_relat_1(k6_relat_1(A_246), B_247)), D_245), A_246) | ~r2_hidden(D_245, k10_relat_1(k6_relat_1(A_246), B_247)) | ~v1_funct_1(k6_relat_1(k10_relat_1(k6_relat_1(A_246), B_247))) | ~v1_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(A_246), B_247))))), inference(superposition, [status(thm), theory('equality')], [c_140, c_1631])).
% 5.00/1.97  tff(c_1727, plain, (![A_248, B_249, D_250]: (r2_hidden(k1_funct_1(k6_relat_1(k10_relat_1(k6_relat_1(A_248), B_249)), D_250), A_248) | ~r2_hidden(D_250, k10_relat_1(k6_relat_1(A_248), B_249)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_1698])).
% 5.00/1.97  tff(c_1755, plain, (![A_39, D_250]: (r2_hidden(k1_funct_1(k6_relat_1(A_39), D_250), A_39) | ~r2_hidden(D_250, k10_relat_1(k6_relat_1(A_39), A_39)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_1727])).
% 5.00/1.97  tff(c_1816, plain, (![A_254, D_255]: (r2_hidden(k1_funct_1(k6_relat_1(A_254), D_255), A_254) | ~r2_hidden(D_255, A_254))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1755])).
% 5.00/1.97  tff(c_1858, plain, (![A_256, D_257, B_258]: (r2_hidden(k1_funct_1(k6_relat_1(A_256), D_257), B_258) | ~r1_tarski(A_256, B_258) | ~r2_hidden(D_257, A_256))), inference(resolution, [status(thm)], [c_1816, c_2])).
% 5.00/1.97  tff(c_36, plain, (![D_51, A_40, B_47]: (r2_hidden(D_51, k10_relat_1(A_40, B_47)) | ~r2_hidden(k1_funct_1(A_40, D_51), B_47) | ~r2_hidden(D_51, k1_relat_1(A_40)) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.00/1.97  tff(c_1881, plain, (![D_257, A_256, B_258]: (r2_hidden(D_257, k10_relat_1(k6_relat_1(A_256), B_258)) | ~r2_hidden(D_257, k1_relat_1(k6_relat_1(A_256))) | ~v1_funct_1(k6_relat_1(A_256)) | ~v1_relat_1(k6_relat_1(A_256)) | ~r1_tarski(A_256, B_258) | ~r2_hidden(D_257, A_256))), inference(resolution, [status(thm)], [c_1858, c_36])).
% 5.00/1.97  tff(c_1908, plain, (![D_262, A_263, B_264]: (r2_hidden(D_262, k10_relat_1(k6_relat_1(A_263), B_264)) | ~r1_tarski(A_263, B_264) | ~r2_hidden(D_262, A_263))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_32, c_1881])).
% 5.00/1.97  tff(c_2760, plain, (![A_319, A_320, B_321]: (r1_tarski(A_319, k10_relat_1(k6_relat_1(A_320), B_321)) | ~r1_tarski(A_320, B_321) | ~r2_hidden('#skF_1'(A_319, k10_relat_1(k6_relat_1(A_320), B_321)), A_320))), inference(resolution, [status(thm)], [c_1908, c_4])).
% 5.00/1.97  tff(c_2842, plain, (![A_322, B_323]: (~r1_tarski(A_322, B_323) | r1_tarski(A_322, k10_relat_1(k6_relat_1(A_322), B_323)))), inference(resolution, [status(thm)], [c_6, c_2760])).
% 5.00/1.97  tff(c_809, plain, (![A_39, B_172, B_173]: (r2_hidden('#skF_1'(k10_relat_1(k6_relat_1(A_39), B_172), B_173), A_39) | ~v1_funct_1(k6_relat_1(A_39)) | ~v1_relat_1(k6_relat_1(A_39)) | r1_tarski(k10_relat_1(k6_relat_1(A_39), B_172), B_173))), inference(superposition, [status(thm), theory('equality')], [c_32, c_782])).
% 5.00/1.97  tff(c_1007, plain, (![A_189, B_190, B_191]: (r2_hidden('#skF_1'(k10_relat_1(k6_relat_1(A_189), B_190), B_191), A_189) | r1_tarski(k10_relat_1(k6_relat_1(A_189), B_190), B_191))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_809])).
% 5.00/1.97  tff(c_1397, plain, (![A_221, B_222, B_223, B_224]: (r2_hidden('#skF_1'(k10_relat_1(k6_relat_1(A_221), B_222), B_223), B_224) | ~r1_tarski(A_221, B_224) | r1_tarski(k10_relat_1(k6_relat_1(A_221), B_222), B_223))), inference(resolution, [status(thm)], [c_1007, c_2])).
% 5.00/1.97  tff(c_1436, plain, (![A_225, B_226, B_227]: (~r1_tarski(A_225, B_226) | r1_tarski(k10_relat_1(k6_relat_1(A_225), B_227), B_226))), inference(resolution, [status(thm)], [c_1397, c_4])).
% 5.00/1.97  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.00/1.97  tff(c_1482, plain, (![A_225, B_227, B_226]: (k10_relat_1(k6_relat_1(A_225), B_227)=B_226 | ~r1_tarski(B_226, k10_relat_1(k6_relat_1(A_225), B_227)) | ~r1_tarski(A_225, B_226))), inference(resolution, [status(thm)], [c_1436, c_8])).
% 5.00/1.97  tff(c_2861, plain, (![A_322, B_323]: (k10_relat_1(k6_relat_1(A_322), B_323)=A_322 | ~r1_tarski(A_322, A_322) | ~r1_tarski(A_322, B_323))), inference(resolution, [status(thm)], [c_2842, c_1482])).
% 5.00/1.97  tff(c_3043, plain, (![A_328, B_329]: (k10_relat_1(k6_relat_1(A_328), B_329)=A_328 | ~r1_tarski(A_328, B_329))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2861])).
% 5.00/1.97  tff(c_28, plain, (![A_37]: (k9_relat_1(A_37, k1_relat_1(A_37))=k2_relat_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.00/1.97  tff(c_326, plain, (![A_123, B_124]: (k3_xboole_0(A_123, k9_relat_1(B_124, k1_relat_1(B_124)))=k9_relat_1(B_124, k10_relat_1(B_124, A_123)) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.00/1.97  tff(c_335, plain, (![A_37, A_123]: (k9_relat_1(A_37, k10_relat_1(A_37, A_123))=k3_xboole_0(A_123, k2_relat_1(A_37)) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_28, c_326])).
% 5.00/1.97  tff(c_3185, plain, (![A_328, B_329]: (k9_relat_1(k6_relat_1(A_328), A_328)=k3_xboole_0(B_329, k2_relat_1(k6_relat_1(A_328))) | ~v1_funct_1(k6_relat_1(A_328)) | ~v1_relat_1(k6_relat_1(A_328)) | ~v1_relat_1(k6_relat_1(A_328)) | ~r1_tarski(A_328, B_329))), inference(superposition, [status(thm), theory('equality')], [c_3043, c_335])).
% 5.00/1.97  tff(c_3277, plain, (![B_330, A_331]: (k3_xboole_0(B_330, A_331)=A_331 | ~r1_tarski(A_331, B_330))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_56, c_154, c_34, c_3185])).
% 5.00/1.97  tff(c_3312, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_3277])).
% 5.00/1.97  tff(c_58, plain, (![A_53, C_55, B_54]: (k3_xboole_0(A_53, k10_relat_1(C_55, B_54))=k10_relat_1(k7_relat_1(C_55, A_53), B_54) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.00/1.97  tff(c_3318, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3312, c_58])).
% 5.00/1.97  tff(c_3325, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3318])).
% 5.00/1.97  tff(c_3327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_3325])).
% 5.00/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.97  
% 5.00/1.97  Inference rules
% 5.00/1.97  ----------------------
% 5.00/1.97  #Ref     : 0
% 5.00/1.97  #Sup     : 724
% 5.00/1.97  #Fact    : 0
% 5.00/1.97  #Define  : 0
% 5.00/1.97  #Split   : 1
% 5.00/1.97  #Chain   : 0
% 5.00/1.97  #Close   : 0
% 5.00/1.97  
% 5.00/1.97  Ordering : KBO
% 5.00/1.97  
% 5.00/1.97  Simplification rules
% 5.00/1.97  ----------------------
% 5.00/1.97  #Subsume      : 152
% 5.00/1.97  #Demod        : 488
% 5.00/1.97  #Tautology    : 131
% 5.00/1.97  #SimpNegUnit  : 1
% 5.00/1.97  #BackRed      : 0
% 5.00/1.97  
% 5.00/1.97  #Partial instantiations: 0
% 5.00/1.97  #Strategies tried      : 1
% 5.00/1.97  
% 5.00/1.97  Timing (in seconds)
% 5.00/1.97  ----------------------
% 5.00/1.97  Preprocessing        : 0.34
% 5.00/1.97  Parsing              : 0.18
% 5.00/1.97  CNF conversion       : 0.03
% 5.00/1.97  Main loop            : 0.86
% 5.00/1.97  Inferencing          : 0.29
% 5.00/1.97  Reduction            : 0.28
% 5.00/1.97  Demodulation         : 0.19
% 5.00/1.97  BG Simplification    : 0.04
% 5.00/1.97  Subsumption          : 0.20
% 5.00/1.97  Abstraction          : 0.04
% 5.00/1.97  MUC search           : 0.00
% 5.00/1.97  Cooper               : 0.00
% 5.00/1.97  Total                : 1.23
% 5.00/1.97  Index Insertion      : 0.00
% 5.00/1.97  Index Deletion       : 0.00
% 5.00/1.97  Index Matching       : 0.00
% 5.00/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
