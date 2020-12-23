%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:35 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :   62 (  84 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   21
%              Number of atoms          :  201 ( 299 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_wellord2 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_wellord2,type,(
    r2_wellord2: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_wellord2(A,B)
          & r2_wellord2(B,C) )
       => r2_wellord2(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_wellord2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r2_wellord2(A,B)
    <=> ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & v2_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B)
        & v2_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v2_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_34,plain,(
    ~ r2_wellord2('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    r2_wellord2('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    r2_wellord2('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( v1_funct_1('#skF_1'(A_14,B_15))
      | ~ r2_wellord2(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1('#skF_1'(A_14,B_15))
      | ~ r2_wellord2(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( v2_funct_1('#skF_1'(A_14,B_15))
      | ~ r2_wellord2(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( k1_relat_1('#skF_1'(A_14,B_15)) = A_14
      | ~ r2_wellord2(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( k2_relat_1('#skF_1'(A_14,B_15)) = B_15
      | ~ r2_wellord2(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( v1_funct_1(k5_relat_1(A_10,B_11))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k5_relat_1(A_10,B_11))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( v2_funct_1(k5_relat_1(A_12,B_13))
      | ~ v2_funct_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_32] :
      ( k9_relat_1(A_32,k1_relat_1(A_32)) = k2_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,(
    ! [A_44,B_45] :
      ( k9_relat_1('#skF_1'(A_44,B_45),A_44) = k2_relat_1('#skF_1'(A_44,B_45))
      | ~ v1_relat_1('#skF_1'(A_44,B_45))
      | ~ r2_wellord2(A_44,B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_69])).

tff(c_114,plain,(
    ! [A_46,B_47] :
      ( k9_relat_1('#skF_1'(A_46,B_47),A_46) = k2_relat_1('#skF_1'(A_46,B_47))
      | ~ r2_wellord2(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_32,c_110])).

tff(c_10,plain,(
    ! [B_6,A_4] :
      ( k9_relat_1(B_6,k2_relat_1(A_4)) = k2_relat_1(k5_relat_1(A_4,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_121,plain,(
    ! [A_4,B_47] :
      ( k2_relat_1(k5_relat_1(A_4,'#skF_1'(k2_relat_1(A_4),B_47))) = k2_relat_1('#skF_1'(k2_relat_1(A_4),B_47))
      | ~ v1_relat_1('#skF_1'(k2_relat_1(A_4),B_47))
      | ~ v1_relat_1(A_4)
      | ~ r2_wellord2(k2_relat_1(A_4),B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_10])).

tff(c_102,plain,(
    ! [A_40,B_41] :
      ( k1_relat_1(k5_relat_1(A_40,B_41)) = k1_relat_1(A_40)
      | ~ r1_tarski(k2_relat_1(A_40),k1_relat_1(B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_157,plain,(
    ! [A_55,A_56,B_57] :
      ( k1_relat_1(k5_relat_1(A_55,'#skF_1'(A_56,B_57))) = k1_relat_1(A_55)
      | ~ r1_tarski(k2_relat_1(A_55),A_56)
      | ~ v1_relat_1('#skF_1'(A_56,B_57))
      | ~ v1_relat_1(A_55)
      | ~ r2_wellord2(A_56,B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_102])).

tff(c_22,plain,(
    ! [C_18] :
      ( r2_wellord2(k1_relat_1(C_18),k2_relat_1(C_18))
      | ~ v2_funct_1(C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1131,plain,(
    ! [A_153,A_154,B_155] :
      ( r2_wellord2(k1_relat_1(A_153),k2_relat_1(k5_relat_1(A_153,'#skF_1'(A_154,B_155))))
      | ~ v2_funct_1(k5_relat_1(A_153,'#skF_1'(A_154,B_155)))
      | ~ v1_funct_1(k5_relat_1(A_153,'#skF_1'(A_154,B_155)))
      | ~ v1_relat_1(k5_relat_1(A_153,'#skF_1'(A_154,B_155)))
      | ~ r1_tarski(k2_relat_1(A_153),A_154)
      | ~ v1_relat_1('#skF_1'(A_154,B_155))
      | ~ v1_relat_1(A_153)
      | ~ r2_wellord2(A_154,B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_22])).

tff(c_1162,plain,(
    ! [A_4,B_47] :
      ( r2_wellord2(k1_relat_1(A_4),k2_relat_1('#skF_1'(k2_relat_1(A_4),B_47)))
      | ~ v2_funct_1(k5_relat_1(A_4,'#skF_1'(k2_relat_1(A_4),B_47)))
      | ~ v1_funct_1(k5_relat_1(A_4,'#skF_1'(k2_relat_1(A_4),B_47)))
      | ~ v1_relat_1(k5_relat_1(A_4,'#skF_1'(k2_relat_1(A_4),B_47)))
      | ~ r1_tarski(k2_relat_1(A_4),k2_relat_1(A_4))
      | ~ v1_relat_1('#skF_1'(k2_relat_1(A_4),B_47))
      | ~ v1_relat_1(A_4)
      | ~ r2_wellord2(k2_relat_1(A_4),B_47)
      | ~ v1_relat_1('#skF_1'(k2_relat_1(A_4),B_47))
      | ~ v1_relat_1(A_4)
      | ~ r2_wellord2(k2_relat_1(A_4),B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_1131])).

tff(c_1286,plain,(
    ! [A_159,B_160] :
      ( r2_wellord2(k1_relat_1(A_159),k2_relat_1('#skF_1'(k2_relat_1(A_159),B_160)))
      | ~ v2_funct_1(k5_relat_1(A_159,'#skF_1'(k2_relat_1(A_159),B_160)))
      | ~ v1_funct_1(k5_relat_1(A_159,'#skF_1'(k2_relat_1(A_159),B_160)))
      | ~ v1_relat_1(k5_relat_1(A_159,'#skF_1'(k2_relat_1(A_159),B_160)))
      | ~ v1_relat_1('#skF_1'(k2_relat_1(A_159),B_160))
      | ~ v1_relat_1(A_159)
      | ~ r2_wellord2(k2_relat_1(A_159),B_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1162])).

tff(c_1351,plain,(
    ! [A_161,B_162] :
      ( r2_wellord2(k1_relat_1(A_161),B_162)
      | ~ v2_funct_1(k5_relat_1(A_161,'#skF_1'(k2_relat_1(A_161),B_162)))
      | ~ v1_funct_1(k5_relat_1(A_161,'#skF_1'(k2_relat_1(A_161),B_162)))
      | ~ v1_relat_1(k5_relat_1(A_161,'#skF_1'(k2_relat_1(A_161),B_162)))
      | ~ v1_relat_1('#skF_1'(k2_relat_1(A_161),B_162))
      | ~ v1_relat_1(A_161)
      | ~ r2_wellord2(k2_relat_1(A_161),B_162)
      | ~ r2_wellord2(k2_relat_1(A_161),B_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1286])).

tff(c_1983,plain,(
    ! [A_202,B_203] :
      ( r2_wellord2(k1_relat_1(A_202),B_203)
      | ~ v1_funct_1(k5_relat_1(A_202,'#skF_1'(k2_relat_1(A_202),B_203)))
      | ~ v1_relat_1(k5_relat_1(A_202,'#skF_1'(k2_relat_1(A_202),B_203)))
      | ~ r2_wellord2(k2_relat_1(A_202),B_203)
      | ~ v2_funct_1('#skF_1'(k2_relat_1(A_202),B_203))
      | ~ v1_funct_1('#skF_1'(k2_relat_1(A_202),B_203))
      | ~ v1_relat_1('#skF_1'(k2_relat_1(A_202),B_203))
      | ~ v2_funct_1(A_202)
      | ~ v1_funct_1(A_202)
      | ~ v1_relat_1(A_202) ) ),
    inference(resolution,[status(thm)],[c_18,c_1351])).

tff(c_2034,plain,(
    ! [A_204,B_205] :
      ( r2_wellord2(k1_relat_1(A_204),B_205)
      | ~ v1_funct_1(k5_relat_1(A_204,'#skF_1'(k2_relat_1(A_204),B_205)))
      | ~ r2_wellord2(k2_relat_1(A_204),B_205)
      | ~ v2_funct_1('#skF_1'(k2_relat_1(A_204),B_205))
      | ~ v2_funct_1(A_204)
      | ~ v1_funct_1('#skF_1'(k2_relat_1(A_204),B_205))
      | ~ v1_relat_1('#skF_1'(k2_relat_1(A_204),B_205))
      | ~ v1_funct_1(A_204)
      | ~ v1_relat_1(A_204) ) ),
    inference(resolution,[status(thm)],[c_16,c_1983])).

tff(c_2085,plain,(
    ! [A_206,B_207] :
      ( r2_wellord2(k1_relat_1(A_206),B_207)
      | ~ r2_wellord2(k2_relat_1(A_206),B_207)
      | ~ v2_funct_1('#skF_1'(k2_relat_1(A_206),B_207))
      | ~ v2_funct_1(A_206)
      | ~ v1_funct_1('#skF_1'(k2_relat_1(A_206),B_207))
      | ~ v1_relat_1('#skF_1'(k2_relat_1(A_206),B_207))
      | ~ v1_funct_1(A_206)
      | ~ v1_relat_1(A_206) ) ),
    inference(resolution,[status(thm)],[c_14,c_2034])).

tff(c_2136,plain,(
    ! [A_208,B_209] :
      ( r2_wellord2(k1_relat_1(A_208),B_209)
      | ~ v2_funct_1(A_208)
      | ~ v1_funct_1('#skF_1'(k2_relat_1(A_208),B_209))
      | ~ v1_relat_1('#skF_1'(k2_relat_1(A_208),B_209))
      | ~ v1_funct_1(A_208)
      | ~ v1_relat_1(A_208)
      | ~ r2_wellord2(k2_relat_1(A_208),B_209) ) ),
    inference(resolution,[status(thm)],[c_28,c_2085])).

tff(c_2272,plain,(
    ! [A_212,B_213] :
      ( r2_wellord2(k1_relat_1(A_212),B_213)
      | ~ v2_funct_1(A_212)
      | ~ v1_funct_1('#skF_1'(k2_relat_1(A_212),B_213))
      | ~ v1_funct_1(A_212)
      | ~ v1_relat_1(A_212)
      | ~ r2_wellord2(k2_relat_1(A_212),B_213) ) ),
    inference(resolution,[status(thm)],[c_32,c_2136])).

tff(c_2323,plain,(
    ! [A_214,B_215] :
      ( r2_wellord2(k1_relat_1(A_214),B_215)
      | ~ v2_funct_1(A_214)
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214)
      | ~ r2_wellord2(k2_relat_1(A_214),B_215) ) ),
    inference(resolution,[status(thm)],[c_30,c_2272])).

tff(c_2379,plain,(
    ! [A_216,B_217,B_218] :
      ( r2_wellord2(k1_relat_1('#skF_1'(A_216,B_217)),B_218)
      | ~ v2_funct_1('#skF_1'(A_216,B_217))
      | ~ v1_funct_1('#skF_1'(A_216,B_217))
      | ~ v1_relat_1('#skF_1'(A_216,B_217))
      | ~ r2_wellord2(B_217,B_218)
      | ~ r2_wellord2(A_216,B_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2323])).

tff(c_2391,plain,(
    ! [A_221,B_222,B_223] :
      ( r2_wellord2(A_221,B_222)
      | ~ v2_funct_1('#skF_1'(A_221,B_223))
      | ~ v1_funct_1('#skF_1'(A_221,B_223))
      | ~ v1_relat_1('#skF_1'(A_221,B_223))
      | ~ r2_wellord2(B_223,B_222)
      | ~ r2_wellord2(A_221,B_223)
      | ~ r2_wellord2(A_221,B_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2379])).

tff(c_2395,plain,(
    ! [A_224,B_225,B_226] :
      ( r2_wellord2(A_224,B_225)
      | ~ v1_funct_1('#skF_1'(A_224,B_226))
      | ~ v1_relat_1('#skF_1'(A_224,B_226))
      | ~ r2_wellord2(B_226,B_225)
      | ~ r2_wellord2(A_224,B_226) ) ),
    inference(resolution,[status(thm)],[c_28,c_2391])).

tff(c_2399,plain,(
    ! [A_227,B_228,B_229] :
      ( r2_wellord2(A_227,B_228)
      | ~ v1_funct_1('#skF_1'(A_227,B_229))
      | ~ r2_wellord2(B_229,B_228)
      | ~ r2_wellord2(A_227,B_229) ) ),
    inference(resolution,[status(thm)],[c_32,c_2395])).

tff(c_2403,plain,(
    ! [A_230,B_231,B_232] :
      ( r2_wellord2(A_230,B_231)
      | ~ r2_wellord2(B_232,B_231)
      | ~ r2_wellord2(A_230,B_232) ) ),
    inference(resolution,[status(thm)],[c_30,c_2399])).

tff(c_2446,plain,(
    ! [A_233] :
      ( r2_wellord2(A_233,'#skF_4')
      | ~ r2_wellord2(A_233,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_2403])).

tff(c_2465,plain,(
    r2_wellord2('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_2446])).

tff(c_2473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:36:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/2.35  
% 5.51/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/2.35  %$ r2_wellord2 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.51/2.35  
% 5.51/2.35  %Foreground sorts:
% 5.51/2.35  
% 5.51/2.35  
% 5.51/2.35  %Background operators:
% 5.51/2.35  
% 5.51/2.35  
% 5.51/2.35  %Foreground operators:
% 5.51/2.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.51/2.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.51/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.51/2.35  tff(r2_wellord2, type, r2_wellord2: ($i * $i) > $o).
% 5.51/2.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.51/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.51/2.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.51/2.35  tff('#skF_2', type, '#skF_2': $i).
% 5.51/2.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.51/2.35  tff('#skF_3', type, '#skF_3': $i).
% 5.51/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.51/2.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.51/2.35  tff('#skF_4', type, '#skF_4': $i).
% 5.51/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.51/2.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.51/2.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.51/2.35  
% 5.76/2.36  tff(f_99, negated_conjecture, ~(![A, B, C]: ((r2_wellord2(A, B) & r2_wellord2(B, C)) => r2_wellord2(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_wellord2)).
% 5.76/2.36  tff(f_92, axiom, (![A, B]: (r2_wellord2(A, B) <=> (?[C]: ((((v1_relat_1(C) & v1_funct_1(C)) & v2_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord2)).
% 5.76/2.36  tff(f_63, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 5.76/2.36  tff(f_79, axiom, (![A, B]: ((((((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) & v2_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v2_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_funct_1)).
% 5.76/2.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.76/2.36  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 5.76/2.36  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 5.76/2.36  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 5.76/2.36  tff(c_34, plain, (~r2_wellord2('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.76/2.36  tff(c_38, plain, (r2_wellord2('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.76/2.36  tff(c_36, plain, (r2_wellord2('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.76/2.36  tff(c_30, plain, (![A_14, B_15]: (v1_funct_1('#skF_1'(A_14, B_15)) | ~r2_wellord2(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.76/2.36  tff(c_32, plain, (![A_14, B_15]: (v1_relat_1('#skF_1'(A_14, B_15)) | ~r2_wellord2(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.76/2.36  tff(c_28, plain, (![A_14, B_15]: (v2_funct_1('#skF_1'(A_14, B_15)) | ~r2_wellord2(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.76/2.36  tff(c_26, plain, (![A_14, B_15]: (k1_relat_1('#skF_1'(A_14, B_15))=A_14 | ~r2_wellord2(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.76/2.36  tff(c_24, plain, (![A_14, B_15]: (k2_relat_1('#skF_1'(A_14, B_15))=B_15 | ~r2_wellord2(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.76/2.36  tff(c_14, plain, (![A_10, B_11]: (v1_funct_1(k5_relat_1(A_10, B_11)) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.76/2.36  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k5_relat_1(A_10, B_11)) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.76/2.36  tff(c_18, plain, (![A_12, B_13]: (v2_funct_1(k5_relat_1(A_12, B_13)) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.76/2.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.76/2.36  tff(c_69, plain, (![A_32]: (k9_relat_1(A_32, k1_relat_1(A_32))=k2_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.76/2.36  tff(c_110, plain, (![A_44, B_45]: (k9_relat_1('#skF_1'(A_44, B_45), A_44)=k2_relat_1('#skF_1'(A_44, B_45)) | ~v1_relat_1('#skF_1'(A_44, B_45)) | ~r2_wellord2(A_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_26, c_69])).
% 5.76/2.36  tff(c_114, plain, (![A_46, B_47]: (k9_relat_1('#skF_1'(A_46, B_47), A_46)=k2_relat_1('#skF_1'(A_46, B_47)) | ~r2_wellord2(A_46, B_47))), inference(resolution, [status(thm)], [c_32, c_110])).
% 5.76/2.36  tff(c_10, plain, (![B_6, A_4]: (k9_relat_1(B_6, k2_relat_1(A_4))=k2_relat_1(k5_relat_1(A_4, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.76/2.36  tff(c_121, plain, (![A_4, B_47]: (k2_relat_1(k5_relat_1(A_4, '#skF_1'(k2_relat_1(A_4), B_47)))=k2_relat_1('#skF_1'(k2_relat_1(A_4), B_47)) | ~v1_relat_1('#skF_1'(k2_relat_1(A_4), B_47)) | ~v1_relat_1(A_4) | ~r2_wellord2(k2_relat_1(A_4), B_47))), inference(superposition, [status(thm), theory('equality')], [c_114, c_10])).
% 5.76/2.36  tff(c_102, plain, (![A_40, B_41]: (k1_relat_1(k5_relat_1(A_40, B_41))=k1_relat_1(A_40) | ~r1_tarski(k2_relat_1(A_40), k1_relat_1(B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.76/2.36  tff(c_157, plain, (![A_55, A_56, B_57]: (k1_relat_1(k5_relat_1(A_55, '#skF_1'(A_56, B_57)))=k1_relat_1(A_55) | ~r1_tarski(k2_relat_1(A_55), A_56) | ~v1_relat_1('#skF_1'(A_56, B_57)) | ~v1_relat_1(A_55) | ~r2_wellord2(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_26, c_102])).
% 5.76/2.36  tff(c_22, plain, (![C_18]: (r2_wellord2(k1_relat_1(C_18), k2_relat_1(C_18)) | ~v2_funct_1(C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.76/2.36  tff(c_1131, plain, (![A_153, A_154, B_155]: (r2_wellord2(k1_relat_1(A_153), k2_relat_1(k5_relat_1(A_153, '#skF_1'(A_154, B_155)))) | ~v2_funct_1(k5_relat_1(A_153, '#skF_1'(A_154, B_155))) | ~v1_funct_1(k5_relat_1(A_153, '#skF_1'(A_154, B_155))) | ~v1_relat_1(k5_relat_1(A_153, '#skF_1'(A_154, B_155))) | ~r1_tarski(k2_relat_1(A_153), A_154) | ~v1_relat_1('#skF_1'(A_154, B_155)) | ~v1_relat_1(A_153) | ~r2_wellord2(A_154, B_155))), inference(superposition, [status(thm), theory('equality')], [c_157, c_22])).
% 5.76/2.36  tff(c_1162, plain, (![A_4, B_47]: (r2_wellord2(k1_relat_1(A_4), k2_relat_1('#skF_1'(k2_relat_1(A_4), B_47))) | ~v2_funct_1(k5_relat_1(A_4, '#skF_1'(k2_relat_1(A_4), B_47))) | ~v1_funct_1(k5_relat_1(A_4, '#skF_1'(k2_relat_1(A_4), B_47))) | ~v1_relat_1(k5_relat_1(A_4, '#skF_1'(k2_relat_1(A_4), B_47))) | ~r1_tarski(k2_relat_1(A_4), k2_relat_1(A_4)) | ~v1_relat_1('#skF_1'(k2_relat_1(A_4), B_47)) | ~v1_relat_1(A_4) | ~r2_wellord2(k2_relat_1(A_4), B_47) | ~v1_relat_1('#skF_1'(k2_relat_1(A_4), B_47)) | ~v1_relat_1(A_4) | ~r2_wellord2(k2_relat_1(A_4), B_47))), inference(superposition, [status(thm), theory('equality')], [c_121, c_1131])).
% 5.76/2.36  tff(c_1286, plain, (![A_159, B_160]: (r2_wellord2(k1_relat_1(A_159), k2_relat_1('#skF_1'(k2_relat_1(A_159), B_160))) | ~v2_funct_1(k5_relat_1(A_159, '#skF_1'(k2_relat_1(A_159), B_160))) | ~v1_funct_1(k5_relat_1(A_159, '#skF_1'(k2_relat_1(A_159), B_160))) | ~v1_relat_1(k5_relat_1(A_159, '#skF_1'(k2_relat_1(A_159), B_160))) | ~v1_relat_1('#skF_1'(k2_relat_1(A_159), B_160)) | ~v1_relat_1(A_159) | ~r2_wellord2(k2_relat_1(A_159), B_160))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1162])).
% 5.76/2.36  tff(c_1351, plain, (![A_161, B_162]: (r2_wellord2(k1_relat_1(A_161), B_162) | ~v2_funct_1(k5_relat_1(A_161, '#skF_1'(k2_relat_1(A_161), B_162))) | ~v1_funct_1(k5_relat_1(A_161, '#skF_1'(k2_relat_1(A_161), B_162))) | ~v1_relat_1(k5_relat_1(A_161, '#skF_1'(k2_relat_1(A_161), B_162))) | ~v1_relat_1('#skF_1'(k2_relat_1(A_161), B_162)) | ~v1_relat_1(A_161) | ~r2_wellord2(k2_relat_1(A_161), B_162) | ~r2_wellord2(k2_relat_1(A_161), B_162))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1286])).
% 5.76/2.36  tff(c_1983, plain, (![A_202, B_203]: (r2_wellord2(k1_relat_1(A_202), B_203) | ~v1_funct_1(k5_relat_1(A_202, '#skF_1'(k2_relat_1(A_202), B_203))) | ~v1_relat_1(k5_relat_1(A_202, '#skF_1'(k2_relat_1(A_202), B_203))) | ~r2_wellord2(k2_relat_1(A_202), B_203) | ~v2_funct_1('#skF_1'(k2_relat_1(A_202), B_203)) | ~v1_funct_1('#skF_1'(k2_relat_1(A_202), B_203)) | ~v1_relat_1('#skF_1'(k2_relat_1(A_202), B_203)) | ~v2_funct_1(A_202) | ~v1_funct_1(A_202) | ~v1_relat_1(A_202))), inference(resolution, [status(thm)], [c_18, c_1351])).
% 5.76/2.36  tff(c_2034, plain, (![A_204, B_205]: (r2_wellord2(k1_relat_1(A_204), B_205) | ~v1_funct_1(k5_relat_1(A_204, '#skF_1'(k2_relat_1(A_204), B_205))) | ~r2_wellord2(k2_relat_1(A_204), B_205) | ~v2_funct_1('#skF_1'(k2_relat_1(A_204), B_205)) | ~v2_funct_1(A_204) | ~v1_funct_1('#skF_1'(k2_relat_1(A_204), B_205)) | ~v1_relat_1('#skF_1'(k2_relat_1(A_204), B_205)) | ~v1_funct_1(A_204) | ~v1_relat_1(A_204))), inference(resolution, [status(thm)], [c_16, c_1983])).
% 5.76/2.36  tff(c_2085, plain, (![A_206, B_207]: (r2_wellord2(k1_relat_1(A_206), B_207) | ~r2_wellord2(k2_relat_1(A_206), B_207) | ~v2_funct_1('#skF_1'(k2_relat_1(A_206), B_207)) | ~v2_funct_1(A_206) | ~v1_funct_1('#skF_1'(k2_relat_1(A_206), B_207)) | ~v1_relat_1('#skF_1'(k2_relat_1(A_206), B_207)) | ~v1_funct_1(A_206) | ~v1_relat_1(A_206))), inference(resolution, [status(thm)], [c_14, c_2034])).
% 5.76/2.36  tff(c_2136, plain, (![A_208, B_209]: (r2_wellord2(k1_relat_1(A_208), B_209) | ~v2_funct_1(A_208) | ~v1_funct_1('#skF_1'(k2_relat_1(A_208), B_209)) | ~v1_relat_1('#skF_1'(k2_relat_1(A_208), B_209)) | ~v1_funct_1(A_208) | ~v1_relat_1(A_208) | ~r2_wellord2(k2_relat_1(A_208), B_209))), inference(resolution, [status(thm)], [c_28, c_2085])).
% 5.76/2.36  tff(c_2272, plain, (![A_212, B_213]: (r2_wellord2(k1_relat_1(A_212), B_213) | ~v2_funct_1(A_212) | ~v1_funct_1('#skF_1'(k2_relat_1(A_212), B_213)) | ~v1_funct_1(A_212) | ~v1_relat_1(A_212) | ~r2_wellord2(k2_relat_1(A_212), B_213))), inference(resolution, [status(thm)], [c_32, c_2136])).
% 5.76/2.36  tff(c_2323, plain, (![A_214, B_215]: (r2_wellord2(k1_relat_1(A_214), B_215) | ~v2_funct_1(A_214) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214) | ~r2_wellord2(k2_relat_1(A_214), B_215))), inference(resolution, [status(thm)], [c_30, c_2272])).
% 5.76/2.36  tff(c_2379, plain, (![A_216, B_217, B_218]: (r2_wellord2(k1_relat_1('#skF_1'(A_216, B_217)), B_218) | ~v2_funct_1('#skF_1'(A_216, B_217)) | ~v1_funct_1('#skF_1'(A_216, B_217)) | ~v1_relat_1('#skF_1'(A_216, B_217)) | ~r2_wellord2(B_217, B_218) | ~r2_wellord2(A_216, B_217))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2323])).
% 5.76/2.36  tff(c_2391, plain, (![A_221, B_222, B_223]: (r2_wellord2(A_221, B_222) | ~v2_funct_1('#skF_1'(A_221, B_223)) | ~v1_funct_1('#skF_1'(A_221, B_223)) | ~v1_relat_1('#skF_1'(A_221, B_223)) | ~r2_wellord2(B_223, B_222) | ~r2_wellord2(A_221, B_223) | ~r2_wellord2(A_221, B_223))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2379])).
% 5.76/2.36  tff(c_2395, plain, (![A_224, B_225, B_226]: (r2_wellord2(A_224, B_225) | ~v1_funct_1('#skF_1'(A_224, B_226)) | ~v1_relat_1('#skF_1'(A_224, B_226)) | ~r2_wellord2(B_226, B_225) | ~r2_wellord2(A_224, B_226))), inference(resolution, [status(thm)], [c_28, c_2391])).
% 5.76/2.36  tff(c_2399, plain, (![A_227, B_228, B_229]: (r2_wellord2(A_227, B_228) | ~v1_funct_1('#skF_1'(A_227, B_229)) | ~r2_wellord2(B_229, B_228) | ~r2_wellord2(A_227, B_229))), inference(resolution, [status(thm)], [c_32, c_2395])).
% 5.76/2.36  tff(c_2403, plain, (![A_230, B_231, B_232]: (r2_wellord2(A_230, B_231) | ~r2_wellord2(B_232, B_231) | ~r2_wellord2(A_230, B_232))), inference(resolution, [status(thm)], [c_30, c_2399])).
% 5.76/2.36  tff(c_2446, plain, (![A_233]: (r2_wellord2(A_233, '#skF_4') | ~r2_wellord2(A_233, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_2403])).
% 5.76/2.36  tff(c_2465, plain, (r2_wellord2('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_2446])).
% 5.76/2.36  tff(c_2473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_2465])).
% 5.76/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.36  
% 5.76/2.36  Inference rules
% 5.76/2.36  ----------------------
% 5.76/2.36  #Ref     : 0
% 5.76/2.36  #Sup     : 710
% 5.76/2.36  #Fact    : 0
% 5.76/2.36  #Define  : 0
% 5.76/2.36  #Split   : 0
% 5.76/2.36  #Chain   : 0
% 5.76/2.36  #Close   : 0
% 5.76/2.36  
% 5.76/2.36  Ordering : KBO
% 5.76/2.36  
% 5.76/2.36  Simplification rules
% 5.76/2.36  ----------------------
% 5.76/2.36  #Subsume      : 62
% 5.76/2.36  #Demod        : 5
% 5.76/2.36  #Tautology    : 89
% 5.76/2.36  #SimpNegUnit  : 1
% 5.76/2.36  #BackRed      : 0
% 5.76/2.36  
% 5.76/2.36  #Partial instantiations: 0
% 5.76/2.36  #Strategies tried      : 1
% 5.76/2.36  
% 5.76/2.36  Timing (in seconds)
% 5.76/2.36  ----------------------
% 5.76/2.37  Preprocessing        : 0.48
% 5.76/2.37  Parsing              : 0.24
% 5.76/2.37  CNF conversion       : 0.03
% 5.76/2.37  Main loop            : 1.00
% 5.76/2.37  Inferencing          : 0.39
% 5.76/2.37  Reduction            : 0.24
% 5.76/2.37  Demodulation         : 0.17
% 5.76/2.37  BG Simplification    : 0.07
% 5.76/2.37  Subsumption          : 0.25
% 5.76/2.37  Abstraction          : 0.07
% 5.76/2.37  MUC search           : 0.00
% 5.76/2.37  Cooper               : 0.00
% 5.76/2.37  Total                : 1.52
% 5.76/2.37  Index Insertion      : 0.00
% 5.76/2.37  Index Deletion       : 0.00
% 5.76/2.37  Index Matching       : 0.00
% 5.76/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
