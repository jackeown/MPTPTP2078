%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:39 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   80 (  97 expanded)
%              Number of leaves         :   40 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 145 expanded)
%              Number of equality atoms :   35 (  39 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_87,axiom,(
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

tff(c_22,plain,(
    ! [A_31] : k2_zfmisc_1(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_128,plain,(
    ! [A_61,B_62] : ~ r2_hidden(A_61,k2_zfmisc_1(A_61,B_62)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_131,plain,(
    ! [A_31] : ~ r2_hidden(A_31,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_128])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_90,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_94,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_176,plain,(
    ! [A_76,B_77] :
      ( k6_domain_1(A_76,B_77) = k1_tarski(B_77)
      | ~ m1_subset_1(B_77,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_179,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_176])).

tff(c_182,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_179])).

tff(c_92,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_183,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_92])).

tff(c_204,plain,(
    ! [A_138,B_139] :
      ( m1_subset_1(k6_domain_1(A_138,B_139),k1_zfmisc_1(A_138))
      | ~ m1_subset_1(B_139,A_138)
      | v1_xboole_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_213,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_204])).

tff(c_217,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_213])).

tff(c_218,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_217])).

tff(c_483,plain,(
    ! [B_218,A_219] :
      ( ~ v1_subset_1(B_218,A_219)
      | v1_xboole_0(B_218)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(A_219))
      | ~ v1_zfmisc_1(A_219)
      | v1_xboole_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_489,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_218,c_483])).

tff(c_498,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_183,c_489])).

tff(c_499,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_498])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_135,plain,(
    ! [B_63,A_64] :
      ( ~ v1_xboole_0(B_63)
      | B_63 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_138,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_2,c_135])).

tff(c_506,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_499,c_138])).

tff(c_6,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] : k3_enumset1(A_9,A_9,B_10,C_11,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k4_enumset1(A_13,A_13,B_14,C_15,D_16,E_17) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,B_19,C_20,D_21,E_22,F_23) = k4_enumset1(A_18,B_19,C_20,D_21,E_22,F_23) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_640,plain,(
    ! [C_233,F_236,G_232,B_234,D_238,E_235,A_237] : k6_enumset1(A_237,A_237,B_234,C_233,D_238,E_235,F_236,G_232) = k5_enumset1(A_237,B_234,C_233,D_238,E_235,F_236,G_232) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    ! [F_40,H_42,B_36,C_37,D_38,J_46,E_39,G_41] : r2_hidden(J_46,k6_enumset1(J_46,B_36,C_37,D_38,E_39,F_40,G_41,H_42)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_673,plain,(
    ! [F_242,D_239,C_245,A_243,E_240,B_241,G_244] : r2_hidden(A_243,k5_enumset1(A_243,B_241,C_245,D_239,E_240,F_242,G_244)) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_44])).

tff(c_677,plain,(
    ! [B_251,A_246,D_250,F_249,C_247,E_248] : r2_hidden(A_246,k4_enumset1(A_246,B_251,C_247,D_250,E_248,F_249)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_673])).

tff(c_681,plain,(
    ! [A_255,C_256,E_254,B_253,D_252] : r2_hidden(A_255,k3_enumset1(A_255,B_253,C_256,D_252,E_254)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_677])).

tff(c_729,plain,(
    ! [A_266,B_267,C_268,D_269] : r2_hidden(A_266,k2_enumset1(A_266,B_267,C_268,D_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_681])).

tff(c_733,plain,(
    ! [A_270,B_271,C_272] : r2_hidden(A_270,k1_enumset1(A_270,B_271,C_272)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_729])).

tff(c_737,plain,(
    ! [A_273,B_274] : r2_hidden(A_273,k2_tarski(A_273,B_274)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_733])).

tff(c_741,plain,(
    ! [A_275] : r2_hidden(A_275,k1_tarski(A_275)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_737])).

tff(c_744,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_741])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.46  
% 3.39/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.47  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.39/1.47  
% 3.39/1.47  %Foreground sorts:
% 3.39/1.47  
% 3.39/1.47  
% 3.39/1.47  %Background operators:
% 3.39/1.47  
% 3.39/1.47  
% 3.39/1.47  %Foreground operators:
% 3.39/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.39/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.39/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.39/1.47  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.39/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.39/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.39/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.39/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.47  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.39/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.39/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.47  
% 3.39/1.48  tff(f_54, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.39/1.48  tff(f_57, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.39/1.48  tff(f_135, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.39/1.48  tff(f_109, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.39/1.48  tff(f_102, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.39/1.48  tff(f_123, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.39/1.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.39/1.48  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.39/1.48  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.39/1.48  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.39/1.48  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.39/1.48  tff(f_42, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.39/1.48  tff(f_44, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.39/1.48  tff(f_46, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.39/1.48  tff(f_48, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.39/1.48  tff(f_87, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.39/1.48  tff(c_22, plain, (![A_31]: (k2_zfmisc_1(A_31, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.39/1.48  tff(c_128, plain, (![A_61, B_62]: (~r2_hidden(A_61, k2_zfmisc_1(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.39/1.48  tff(c_131, plain, (![A_31]: (~r2_hidden(A_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_128])).
% 3.39/1.48  tff(c_96, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.39/1.48  tff(c_90, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.39/1.48  tff(c_94, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.39/1.48  tff(c_176, plain, (![A_76, B_77]: (k6_domain_1(A_76, B_77)=k1_tarski(B_77) | ~m1_subset_1(B_77, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.39/1.48  tff(c_179, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_94, c_176])).
% 3.39/1.48  tff(c_182, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_96, c_179])).
% 3.39/1.48  tff(c_92, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.39/1.48  tff(c_183, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_92])).
% 3.39/1.48  tff(c_204, plain, (![A_138, B_139]: (m1_subset_1(k6_domain_1(A_138, B_139), k1_zfmisc_1(A_138)) | ~m1_subset_1(B_139, A_138) | v1_xboole_0(A_138))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.39/1.48  tff(c_213, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_182, c_204])).
% 3.39/1.48  tff(c_217, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_213])).
% 3.39/1.48  tff(c_218, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_96, c_217])).
% 3.39/1.48  tff(c_483, plain, (![B_218, A_219]: (~v1_subset_1(B_218, A_219) | v1_xboole_0(B_218) | ~m1_subset_1(B_218, k1_zfmisc_1(A_219)) | ~v1_zfmisc_1(A_219) | v1_xboole_0(A_219))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.39/1.48  tff(c_489, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_218, c_483])).
% 3.39/1.48  tff(c_498, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_183, c_489])).
% 3.39/1.48  tff(c_499, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_96, c_498])).
% 3.39/1.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.39/1.48  tff(c_135, plain, (![B_63, A_64]: (~v1_xboole_0(B_63) | B_63=A_64 | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.39/1.48  tff(c_138, plain, (![A_64]: (k1_xboole_0=A_64 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_2, c_135])).
% 3.39/1.48  tff(c_506, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_499, c_138])).
% 3.39/1.48  tff(c_6, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.39/1.48  tff(c_8, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.48  tff(c_10, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.39/1.48  tff(c_12, plain, (![A_9, B_10, C_11, D_12]: (k3_enumset1(A_9, A_9, B_10, C_11, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.48  tff(c_14, plain, (![E_17, A_13, B_14, C_15, D_16]: (k4_enumset1(A_13, A_13, B_14, C_15, D_16, E_17)=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.39/1.48  tff(c_16, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, D_21, E_22, F_23)=k4_enumset1(A_18, B_19, C_20, D_21, E_22, F_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.39/1.48  tff(c_640, plain, (![C_233, F_236, G_232, B_234, D_238, E_235, A_237]: (k6_enumset1(A_237, A_237, B_234, C_233, D_238, E_235, F_236, G_232)=k5_enumset1(A_237, B_234, C_233, D_238, E_235, F_236, G_232))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.39/1.48  tff(c_44, plain, (![F_40, H_42, B_36, C_37, D_38, J_46, E_39, G_41]: (r2_hidden(J_46, k6_enumset1(J_46, B_36, C_37, D_38, E_39, F_40, G_41, H_42)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.39/1.48  tff(c_673, plain, (![F_242, D_239, C_245, A_243, E_240, B_241, G_244]: (r2_hidden(A_243, k5_enumset1(A_243, B_241, C_245, D_239, E_240, F_242, G_244)))), inference(superposition, [status(thm), theory('equality')], [c_640, c_44])).
% 3.39/1.48  tff(c_677, plain, (![B_251, A_246, D_250, F_249, C_247, E_248]: (r2_hidden(A_246, k4_enumset1(A_246, B_251, C_247, D_250, E_248, F_249)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_673])).
% 3.39/1.48  tff(c_681, plain, (![A_255, C_256, E_254, B_253, D_252]: (r2_hidden(A_255, k3_enumset1(A_255, B_253, C_256, D_252, E_254)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_677])).
% 3.39/1.48  tff(c_729, plain, (![A_266, B_267, C_268, D_269]: (r2_hidden(A_266, k2_enumset1(A_266, B_267, C_268, D_269)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_681])).
% 3.39/1.48  tff(c_733, plain, (![A_270, B_271, C_272]: (r2_hidden(A_270, k1_enumset1(A_270, B_271, C_272)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_729])).
% 3.39/1.48  tff(c_737, plain, (![A_273, B_274]: (r2_hidden(A_273, k2_tarski(A_273, B_274)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_733])).
% 3.39/1.48  tff(c_741, plain, (![A_275]: (r2_hidden(A_275, k1_tarski(A_275)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_737])).
% 3.39/1.48  tff(c_744, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_506, c_741])).
% 3.39/1.48  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_744])).
% 3.39/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.48  
% 3.39/1.48  Inference rules
% 3.39/1.48  ----------------------
% 3.39/1.48  #Ref     : 0
% 3.39/1.48  #Sup     : 145
% 3.39/1.48  #Fact    : 0
% 3.39/1.48  #Define  : 0
% 3.39/1.48  #Split   : 3
% 3.39/1.48  #Chain   : 0
% 3.39/1.48  #Close   : 0
% 3.39/1.48  
% 3.39/1.48  Ordering : KBO
% 3.39/1.48  
% 3.39/1.48  Simplification rules
% 3.39/1.48  ----------------------
% 3.39/1.48  #Subsume      : 13
% 3.39/1.48  #Demod        : 68
% 3.39/1.48  #Tautology    : 84
% 3.39/1.48  #SimpNegUnit  : 18
% 3.39/1.48  #BackRed      : 15
% 3.39/1.48  
% 3.39/1.48  #Partial instantiations: 0
% 3.39/1.48  #Strategies tried      : 1
% 3.39/1.48  
% 3.39/1.48  Timing (in seconds)
% 3.39/1.48  ----------------------
% 3.39/1.49  Preprocessing        : 0.36
% 3.39/1.49  Parsing              : 0.17
% 3.39/1.49  CNF conversion       : 0.03
% 3.39/1.49  Main loop            : 0.36
% 3.39/1.49  Inferencing          : 0.12
% 3.39/1.49  Reduction            : 0.10
% 3.39/1.49  Demodulation         : 0.07
% 3.39/1.49  BG Simplification    : 0.03
% 3.39/1.49  Subsumption          : 0.10
% 3.39/1.49  Abstraction          : 0.03
% 3.39/1.49  MUC search           : 0.00
% 3.39/1.49  Cooper               : 0.00
% 3.39/1.49  Total                : 0.76
% 3.39/1.49  Index Insertion      : 0.00
% 3.39/1.49  Index Deletion       : 0.00
% 3.39/1.49  Index Matching       : 0.00
% 3.39/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
