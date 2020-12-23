%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:25 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 100 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 155 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_enumset1(A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,D_18,E_19) = k3_enumset1(A_15,B_16,C_17,D_18,E_19) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] : k5_enumset1(A_20,A_20,B_21,C_22,D_23,E_24,F_25) = k4_enumset1(A_20,B_21,C_22,D_23,E_24,F_25) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_198,plain,(
    ! [E_174,A_171,D_169,C_173,G_175,F_172,B_170] : k6_enumset1(A_171,A_171,B_170,C_173,D_169,E_174,F_172,G_175) = k5_enumset1(A_171,B_170,C_173,D_169,E_174,F_172,G_175) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [D_36,G_39,J_44,F_38,E_37,A_33,B_34,C_35] : r2_hidden(J_44,k6_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,G_39,J_44)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_307,plain,(
    ! [G_232,D_231,E_228,A_234,C_229,B_230,F_233] : r2_hidden(G_232,k5_enumset1(A_234,B_230,C_229,D_231,E_228,F_233,G_232)) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_20])).

tff(c_311,plain,(
    ! [E_238,A_239,D_237,C_235,B_236,F_240] : r2_hidden(F_240,k4_enumset1(A_239,B_236,C_235,D_237,E_238,F_240)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_307])).

tff(c_315,plain,(
    ! [E_244,D_242,C_241,B_243,A_245] : r2_hidden(E_244,k3_enumset1(A_245,B_243,C_241,D_242,E_244)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_311])).

tff(c_320,plain,(
    ! [D_255,A_256,B_257,C_258] : r2_hidden(D_255,k2_enumset1(A_256,B_257,C_258,D_255)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_315])).

tff(c_324,plain,(
    ! [C_259,A_260,B_261] : r2_hidden(C_259,k1_enumset1(A_260,B_261,C_259)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_320])).

tff(c_328,plain,(
    ! [B_262,A_263] : r2_hidden(B_262,k2_tarski(A_263,B_262)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_324])).

tff(c_72,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_107,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k1_setfam_1(B_63),A_64)
      | ~ r2_hidden(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_110,plain,(
    ! [A_45,B_46,A_64] :
      ( r1_tarski(k3_xboole_0(A_45,B_46),A_64)
      | ~ r2_hidden(A_64,k2_tarski(A_45,B_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_107])).

tff(c_332,plain,(
    ! [A_263,B_262] : r1_tarski(k3_xboole_0(A_263,B_262),B_262) ),
    inference(resolution,[status(thm)],[c_328,c_110])).

tff(c_86,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_76,plain,(
    ! [A_49,B_50] :
      ( v1_relat_1(k3_xboole_0(A_49,B_50))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_84,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_163,plain,(
    ! [A_156,B_157] :
      ( r1_tarski(k2_relat_1(A_156),k2_relat_1(B_157))
      | ~ r1_tarski(A_156,B_157)
      | ~ v1_relat_1(B_157)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_145,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k2_relat_1(A_144),k2_relat_1(B_145))
      | ~ r1_tarski(A_144,B_145)
      | ~ v1_relat_1(B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_126,plain,(
    ! [A_111,B_112,C_113] :
      ( r1_tarski(A_111,k3_xboole_0(B_112,C_113))
      | ~ r1_tarski(A_111,C_113)
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_130,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_126,c_82])).

tff(c_142,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_148,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_145,c_142])).

tff(c_151,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2,c_148])).

tff(c_154,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_151])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_154])).

tff(c_159,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_166,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_163,c_159])).

tff(c_169,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_166])).

tff(c_170,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_173,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_170])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_173])).

tff(c_178,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:15:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.33  
% 2.96/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.33  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.96/1.33  
% 2.96/1.33  %Foreground sorts:
% 2.96/1.33  
% 2.96/1.33  
% 2.96/1.33  %Background operators:
% 2.96/1.33  
% 2.96/1.33  
% 2.96/1.33  %Foreground operators:
% 2.96/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.96/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.96/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.96/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.96/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.96/1.33  
% 2.96/1.35  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.96/1.35  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.96/1.35  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.96/1.35  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.96/1.35  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.96/1.35  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.96/1.35  tff(f_75, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 2.96/1.35  tff(f_77, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.96/1.35  tff(f_81, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.96/1.35  tff(f_104, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 2.96/1.35  tff(f_85, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.96/1.35  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.96/1.35  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.96/1.35  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.96/1.35  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.35  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.35  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.35  tff(c_12, plain, (![B_16, A_15, D_18, E_19, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, E_19)=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.96/1.35  tff(c_14, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (k5_enumset1(A_20, A_20, B_21, C_22, D_23, E_24, F_25)=k4_enumset1(A_20, B_21, C_22, D_23, E_24, F_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.35  tff(c_198, plain, (![E_174, A_171, D_169, C_173, G_175, F_172, B_170]: (k6_enumset1(A_171, A_171, B_170, C_173, D_169, E_174, F_172, G_175)=k5_enumset1(A_171, B_170, C_173, D_169, E_174, F_172, G_175))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.96/1.35  tff(c_20, plain, (![D_36, G_39, J_44, F_38, E_37, A_33, B_34, C_35]: (r2_hidden(J_44, k6_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, G_39, J_44)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.96/1.35  tff(c_307, plain, (![G_232, D_231, E_228, A_234, C_229, B_230, F_233]: (r2_hidden(G_232, k5_enumset1(A_234, B_230, C_229, D_231, E_228, F_233, G_232)))), inference(superposition, [status(thm), theory('equality')], [c_198, c_20])).
% 2.96/1.35  tff(c_311, plain, (![E_238, A_239, D_237, C_235, B_236, F_240]: (r2_hidden(F_240, k4_enumset1(A_239, B_236, C_235, D_237, E_238, F_240)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_307])).
% 2.96/1.35  tff(c_315, plain, (![E_244, D_242, C_241, B_243, A_245]: (r2_hidden(E_244, k3_enumset1(A_245, B_243, C_241, D_242, E_244)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_311])).
% 2.96/1.35  tff(c_320, plain, (![D_255, A_256, B_257, C_258]: (r2_hidden(D_255, k2_enumset1(A_256, B_257, C_258, D_255)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_315])).
% 2.96/1.35  tff(c_324, plain, (![C_259, A_260, B_261]: (r2_hidden(C_259, k1_enumset1(A_260, B_261, C_259)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_320])).
% 2.96/1.35  tff(c_328, plain, (![B_262, A_263]: (r2_hidden(B_262, k2_tarski(A_263, B_262)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_324])).
% 2.96/1.35  tff(c_72, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.96/1.35  tff(c_107, plain, (![B_63, A_64]: (r1_tarski(k1_setfam_1(B_63), A_64) | ~r2_hidden(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.96/1.35  tff(c_110, plain, (![A_45, B_46, A_64]: (r1_tarski(k3_xboole_0(A_45, B_46), A_64) | ~r2_hidden(A_64, k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_107])).
% 2.96/1.35  tff(c_332, plain, (![A_263, B_262]: (r1_tarski(k3_xboole_0(A_263, B_262), B_262))), inference(resolution, [status(thm)], [c_328, c_110])).
% 2.96/1.35  tff(c_86, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.96/1.35  tff(c_76, plain, (![A_49, B_50]: (v1_relat_1(k3_xboole_0(A_49, B_50)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.96/1.35  tff(c_84, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.96/1.35  tff(c_163, plain, (![A_156, B_157]: (r1_tarski(k2_relat_1(A_156), k2_relat_1(B_157)) | ~r1_tarski(A_156, B_157) | ~v1_relat_1(B_157) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.96/1.35  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.35  tff(c_145, plain, (![A_144, B_145]: (r1_tarski(k2_relat_1(A_144), k2_relat_1(B_145)) | ~r1_tarski(A_144, B_145) | ~v1_relat_1(B_145) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.96/1.35  tff(c_126, plain, (![A_111, B_112, C_113]: (r1_tarski(A_111, k3_xboole_0(B_112, C_113)) | ~r1_tarski(A_111, C_113) | ~r1_tarski(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.35  tff(c_82, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.96/1.35  tff(c_130, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_126, c_82])).
% 2.96/1.35  tff(c_142, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_130])).
% 2.96/1.35  tff(c_148, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_145, c_142])).
% 2.96/1.35  tff(c_151, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2, c_148])).
% 2.96/1.35  tff(c_154, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_151])).
% 2.96/1.35  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_154])).
% 2.96/1.35  tff(c_159, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_130])).
% 2.96/1.35  tff(c_166, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_163, c_159])).
% 2.96/1.35  tff(c_169, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_166])).
% 2.96/1.35  tff(c_170, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_169])).
% 2.96/1.35  tff(c_173, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_170])).
% 2.96/1.35  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_173])).
% 2.96/1.35  tff(c_178, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_169])).
% 2.96/1.35  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_332, c_178])).
% 2.96/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.35  
% 2.96/1.35  Inference rules
% 2.96/1.35  ----------------------
% 2.96/1.35  #Ref     : 0
% 2.96/1.35  #Sup     : 50
% 2.96/1.35  #Fact    : 0
% 2.96/1.35  #Define  : 0
% 2.96/1.35  #Split   : 2
% 2.96/1.35  #Chain   : 0
% 2.96/1.35  #Close   : 0
% 2.96/1.35  
% 2.96/1.35  Ordering : KBO
% 2.96/1.35  
% 2.96/1.35  Simplification rules
% 2.96/1.35  ----------------------
% 2.96/1.35  #Subsume      : 0
% 2.96/1.35  #Demod        : 8
% 2.96/1.35  #Tautology    : 24
% 2.96/1.35  #SimpNegUnit  : 0
% 2.96/1.35  #BackRed      : 1
% 2.96/1.35  
% 2.96/1.35  #Partial instantiations: 0
% 2.96/1.35  #Strategies tried      : 1
% 2.96/1.35  
% 2.96/1.35  Timing (in seconds)
% 2.96/1.35  ----------------------
% 2.96/1.35  Preprocessing        : 0.35
% 2.96/1.35  Parsing              : 0.17
% 2.96/1.35  CNF conversion       : 0.03
% 2.96/1.35  Main loop            : 0.28
% 2.96/1.35  Inferencing          : 0.09
% 2.96/1.35  Reduction            : 0.07
% 2.96/1.35  Demodulation         : 0.05
% 2.96/1.35  BG Simplification    : 0.02
% 2.96/1.35  Subsumption          : 0.09
% 2.96/1.35  Abstraction          : 0.02
% 2.96/1.35  MUC search           : 0.00
% 2.96/1.35  Cooper               : 0.00
% 2.96/1.35  Total                : 0.67
% 2.96/1.35  Index Insertion      : 0.00
% 2.96/1.35  Index Deletion       : 0.00
% 2.96/1.36  Index Matching       : 0.00
% 2.96/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
