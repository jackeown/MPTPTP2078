%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:40 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   73 (  99 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 152 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

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

tff(c_194,plain,(
    ! [C_169,B_166,A_167,E_170,F_168,G_171,D_165] : k6_enumset1(A_167,A_167,B_166,C_169,D_165,E_170,F_168,G_171) = k5_enumset1(A_167,B_166,C_169,D_165,E_170,F_168,G_171) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [D_36,G_39,J_44,F_38,E_37,A_33,B_34,C_35] : r2_hidden(J_44,k6_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,G_39,J_44)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_321,plain,(
    ! [E_266,D_264,B_262,A_265,C_261,G_260,F_263] : r2_hidden(G_260,k5_enumset1(A_265,B_262,C_261,D_264,E_266,F_263,G_260)) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_20])).

tff(c_325,plain,(
    ! [F_272,A_271,E_270,C_267,D_269,B_268] : r2_hidden(F_272,k4_enumset1(A_271,B_268,C_267,D_269,E_270,F_272)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_321])).

tff(c_329,plain,(
    ! [C_273,A_277,D_274,B_275,E_276] : r2_hidden(E_276,k3_enumset1(A_277,B_275,C_273,D_274,E_276)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_325])).

tff(c_333,plain,(
    ! [D_278,A_279,B_280,C_281] : r2_hidden(D_278,k2_enumset1(A_279,B_280,C_281,D_278)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_329])).

tff(c_337,plain,(
    ! [C_282,A_283,B_284] : r2_hidden(C_282,k1_enumset1(A_283,B_284,C_282)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_333])).

tff(c_342,plain,(
    ! [B_294,A_295] : r2_hidden(B_294,k2_tarski(A_295,B_294)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_337])).

tff(c_97,plain,(
    ! [A_63,B_64] : k1_setfam_1(k2_tarski(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,(
    ! [B_48,A_47] :
      ( r1_tarski(k1_setfam_1(B_48),A_47)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_103,plain,(
    ! [A_63,B_64,A_47] :
      ( r1_tarski(k3_xboole_0(A_63,B_64),A_47)
      | ~ r2_hidden(A_47,k2_tarski(A_63,B_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_74])).

tff(c_346,plain,(
    ! [A_295,B_294] : r1_tarski(k3_xboole_0(A_295,B_294),B_294) ),
    inference(resolution,[status(thm)],[c_342,c_103])).

tff(c_84,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_76,plain,(
    ! [A_49,B_50] :
      ( v1_relat_1(k3_xboole_0(A_49,B_50))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_82,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_159,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(k3_relat_1(A_152),k3_relat_1(B_153))
      | ~ r1_tarski(A_152,B_153)
      | ~ v1_relat_1(B_153)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [A_142,B_143] :
      ( r1_tarski(k3_relat_1(A_142),k3_relat_1(B_143))
      | ~ r1_tarski(A_142,B_143)
      | ~ v1_relat_1(B_143)
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_123,plain,(
    ! [A_103,B_104,C_105] :
      ( r1_tarski(A_103,k3_xboole_0(B_104,C_105))
      | ~ r1_tarski(A_103,C_105)
      | ~ r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_127,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_123,c_80])).

tff(c_140,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_145,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_142,c_140])).

tff(c_148,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2,c_145])).

tff(c_151,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_148])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_151])).

tff(c_156,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_162,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_159,c_156])).

tff(c_165,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_162])).

tff(c_166,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_169,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_169])).

tff(c_174,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.43  
% 2.78/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.43  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.78/1.43  
% 2.78/1.43  %Foreground sorts:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Background operators:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Foreground operators:
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.78/1.43  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.78/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.78/1.43  
% 2.78/1.45  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.78/1.45  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.78/1.45  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.78/1.45  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.78/1.45  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.78/1.45  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.78/1.45  tff(f_75, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 2.78/1.45  tff(f_77, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.78/1.45  tff(f_81, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.78/1.45  tff(f_102, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 2.78/1.45  tff(f_85, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.78/1.45  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.78/1.45  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.78/1.45  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.78/1.45  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.45  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.45  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.45  tff(c_12, plain, (![B_16, A_15, D_18, E_19, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, E_19)=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.45  tff(c_14, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (k5_enumset1(A_20, A_20, B_21, C_22, D_23, E_24, F_25)=k4_enumset1(A_20, B_21, C_22, D_23, E_24, F_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.45  tff(c_194, plain, (![C_169, B_166, A_167, E_170, F_168, G_171, D_165]: (k6_enumset1(A_167, A_167, B_166, C_169, D_165, E_170, F_168, G_171)=k5_enumset1(A_167, B_166, C_169, D_165, E_170, F_168, G_171))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.45  tff(c_20, plain, (![D_36, G_39, J_44, F_38, E_37, A_33, B_34, C_35]: (r2_hidden(J_44, k6_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, G_39, J_44)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.45  tff(c_321, plain, (![E_266, D_264, B_262, A_265, C_261, G_260, F_263]: (r2_hidden(G_260, k5_enumset1(A_265, B_262, C_261, D_264, E_266, F_263, G_260)))), inference(superposition, [status(thm), theory('equality')], [c_194, c_20])).
% 2.78/1.45  tff(c_325, plain, (![F_272, A_271, E_270, C_267, D_269, B_268]: (r2_hidden(F_272, k4_enumset1(A_271, B_268, C_267, D_269, E_270, F_272)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_321])).
% 2.78/1.45  tff(c_329, plain, (![C_273, A_277, D_274, B_275, E_276]: (r2_hidden(E_276, k3_enumset1(A_277, B_275, C_273, D_274, E_276)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_325])).
% 2.78/1.45  tff(c_333, plain, (![D_278, A_279, B_280, C_281]: (r2_hidden(D_278, k2_enumset1(A_279, B_280, C_281, D_278)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_329])).
% 2.78/1.45  tff(c_337, plain, (![C_282, A_283, B_284]: (r2_hidden(C_282, k1_enumset1(A_283, B_284, C_282)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_333])).
% 2.78/1.45  tff(c_342, plain, (![B_294, A_295]: (r2_hidden(B_294, k2_tarski(A_295, B_294)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_337])).
% 2.78/1.45  tff(c_97, plain, (![A_63, B_64]: (k1_setfam_1(k2_tarski(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.78/1.45  tff(c_74, plain, (![B_48, A_47]: (r1_tarski(k1_setfam_1(B_48), A_47) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.78/1.45  tff(c_103, plain, (![A_63, B_64, A_47]: (r1_tarski(k3_xboole_0(A_63, B_64), A_47) | ~r2_hidden(A_47, k2_tarski(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_74])).
% 2.78/1.45  tff(c_346, plain, (![A_295, B_294]: (r1_tarski(k3_xboole_0(A_295, B_294), B_294))), inference(resolution, [status(thm)], [c_342, c_103])).
% 2.78/1.45  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.78/1.45  tff(c_76, plain, (![A_49, B_50]: (v1_relat_1(k3_xboole_0(A_49, B_50)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.78/1.45  tff(c_82, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.78/1.45  tff(c_159, plain, (![A_152, B_153]: (r1_tarski(k3_relat_1(A_152), k3_relat_1(B_153)) | ~r1_tarski(A_152, B_153) | ~v1_relat_1(B_153) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.45  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.45  tff(c_142, plain, (![A_142, B_143]: (r1_tarski(k3_relat_1(A_142), k3_relat_1(B_143)) | ~r1_tarski(A_142, B_143) | ~v1_relat_1(B_143) | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.45  tff(c_123, plain, (![A_103, B_104, C_105]: (r1_tarski(A_103, k3_xboole_0(B_104, C_105)) | ~r1_tarski(A_103, C_105) | ~r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.45  tff(c_80, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.78/1.45  tff(c_127, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_123, c_80])).
% 2.78/1.45  tff(c_140, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_127])).
% 2.78/1.45  tff(c_145, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_142, c_140])).
% 2.78/1.45  tff(c_148, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2, c_145])).
% 2.78/1.45  tff(c_151, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_148])).
% 2.78/1.45  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_151])).
% 2.78/1.45  tff(c_156, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_127])).
% 2.78/1.45  tff(c_162, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_159, c_156])).
% 2.78/1.45  tff(c_165, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_162])).
% 2.78/1.45  tff(c_166, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_165])).
% 2.78/1.45  tff(c_169, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_166])).
% 2.78/1.45  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_169])).
% 2.78/1.45  tff(c_174, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_165])).
% 2.78/1.45  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_346, c_174])).
% 2.78/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.45  
% 2.78/1.45  Inference rules
% 2.78/1.45  ----------------------
% 2.78/1.45  #Ref     : 0
% 2.78/1.45  #Sup     : 54
% 2.78/1.45  #Fact    : 0
% 2.78/1.45  #Define  : 0
% 2.78/1.45  #Split   : 2
% 2.78/1.45  #Chain   : 0
% 2.78/1.45  #Close   : 0
% 2.78/1.45  
% 2.78/1.45  Ordering : KBO
% 2.78/1.45  
% 2.78/1.45  Simplification rules
% 2.78/1.45  ----------------------
% 2.78/1.45  #Subsume      : 0
% 2.78/1.45  #Demod        : 8
% 2.78/1.45  #Tautology    : 24
% 2.78/1.45  #SimpNegUnit  : 0
% 2.78/1.45  #BackRed      : 1
% 2.78/1.45  
% 2.78/1.45  #Partial instantiations: 0
% 2.78/1.45  #Strategies tried      : 1
% 2.78/1.45  
% 2.78/1.45  Timing (in seconds)
% 2.78/1.45  ----------------------
% 2.78/1.45  Preprocessing        : 0.36
% 2.78/1.45  Parsing              : 0.17
% 2.78/1.45  CNF conversion       : 0.03
% 2.78/1.45  Main loop            : 0.30
% 2.78/1.45  Inferencing          : 0.10
% 2.78/1.45  Reduction            : 0.08
% 2.78/1.45  Demodulation         : 0.06
% 2.78/1.45  BG Simplification    : 0.02
% 2.78/1.45  Subsumption          : 0.10
% 2.78/1.45  Abstraction          : 0.03
% 2.78/1.45  MUC search           : 0.00
% 2.78/1.45  Cooper               : 0.00
% 2.78/1.45  Total                : 0.70
% 2.78/1.45  Index Insertion      : 0.00
% 2.78/1.45  Index Deletion       : 0.00
% 2.78/1.45  Index Matching       : 0.00
% 2.78/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
