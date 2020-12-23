%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:40 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   77 (  94 expanded)
%              Number of leaves         :   39 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 139 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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

tff(f_88,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_84,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_88,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_122,plain,(
    ! [A_68,B_69] :
      ( k6_domain_1(A_68,B_69) = k1_tarski(B_69)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_125,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_122])).

tff(c_128,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_125])).

tff(c_86,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_129,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_86])).

tff(c_169,plain,(
    ! [A_126,B_127] :
      ( m1_subset_1(k6_domain_1(A_126,B_127),k1_zfmisc_1(A_126))
      | ~ m1_subset_1(B_127,A_126)
      | v1_xboole_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_178,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_169])).

tff(c_182,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_178])).

tff(c_183,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_182])).

tff(c_208,plain,(
    ! [B_140,A_141] :
      ( ~ v1_subset_1(B_140,A_141)
      | v1_xboole_0(B_140)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_141))
      | ~ v1_zfmisc_1(A_141)
      | v1_xboole_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_211,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_183,c_208])).

tff(c_217,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_129,c_211])).

tff(c_218,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_217])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_223,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_218,c_2])).

tff(c_6,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] : k3_enumset1(A_9,A_9,B_10,C_11,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k4_enumset1(A_13,A_13,B_14,C_15,D_16,E_17) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,B_19,C_20,D_21,E_22,F_23) = k4_enumset1(A_18,B_19,C_20,D_21,E_22,F_23) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_347,plain,(
    ! [D_227,F_225,G_221,C_222,E_224,A_226,B_223] : k6_enumset1(A_226,A_226,B_223,C_222,D_227,E_224,F_225,G_221) = k5_enumset1(A_226,B_223,C_222,D_227,E_224,F_225,G_221) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [A_31,B_32,H_38,F_36,E_35,G_37,D_34,J_42] : r2_hidden(J_42,k6_enumset1(A_31,B_32,J_42,D_34,E_35,F_36,G_37,H_38)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_404,plain,(
    ! [D_231,A_234,B_233,F_228,E_229,C_232,G_230] : r2_hidden(B_233,k5_enumset1(A_234,B_233,C_232,D_231,E_229,F_228,G_230)) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_32])).

tff(c_412,plain,(
    ! [A_235,B_240,D_239,C_236,F_238,E_237] : r2_hidden(A_235,k4_enumset1(A_235,B_240,C_236,D_239,E_237,F_238)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_404])).

tff(c_420,plain,(
    ! [A_244,C_245,E_243,B_242,D_241] : r2_hidden(A_244,k3_enumset1(A_244,B_242,C_245,D_241,E_243)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_412])).

tff(c_472,plain,(
    ! [A_255,B_256,C_257,D_258] : r2_hidden(A_255,k2_enumset1(A_255,B_256,C_257,D_258)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_420])).

tff(c_480,plain,(
    ! [A_259,B_260,C_261] : r2_hidden(A_259,k1_enumset1(A_259,B_260,C_261)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_472])).

tff(c_488,plain,(
    ! [A_262,B_263] : r2_hidden(A_262,k2_tarski(A_262,B_263)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_480])).

tff(c_497,plain,(
    ! [A_273] : r2_hidden(A_273,k1_tarski(A_273)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_488])).

tff(c_503,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_497])).

tff(c_76,plain,(
    ! [B_47,A_46] :
      ( ~ r1_tarski(B_47,A_46)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_507,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_503,c_76])).

tff(c_511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.49  
% 3.13/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.49  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.13/1.49  
% 3.13/1.49  %Foreground sorts:
% 3.13/1.49  
% 3.13/1.49  
% 3.13/1.49  %Background operators:
% 3.13/1.49  
% 3.13/1.49  
% 3.13/1.49  %Foreground operators:
% 3.13/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.49  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.13/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.13/1.49  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.13/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.13/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.13/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.13/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.13/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.13/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.49  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.13/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.13/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.13/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.49  
% 3.26/1.51  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.26/1.51  tff(f_128, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.26/1.51  tff(f_102, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.26/1.51  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.26/1.51  tff(f_116, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.26/1.51  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.26/1.51  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.26/1.51  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.26/1.51  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.26/1.51  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.26/1.51  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.26/1.51  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.26/1.51  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.26/1.51  tff(f_75, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 3.26/1.51  tff(f_88, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.26/1.51  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.51  tff(c_90, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.26/1.51  tff(c_84, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.26/1.51  tff(c_88, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.26/1.51  tff(c_122, plain, (![A_68, B_69]: (k6_domain_1(A_68, B_69)=k1_tarski(B_69) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.26/1.51  tff(c_125, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_88, c_122])).
% 3.26/1.51  tff(c_128, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_90, c_125])).
% 3.26/1.51  tff(c_86, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.26/1.51  tff(c_129, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_86])).
% 3.26/1.51  tff(c_169, plain, (![A_126, B_127]: (m1_subset_1(k6_domain_1(A_126, B_127), k1_zfmisc_1(A_126)) | ~m1_subset_1(B_127, A_126) | v1_xboole_0(A_126))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.51  tff(c_178, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_128, c_169])).
% 3.26/1.51  tff(c_182, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_178])).
% 3.26/1.51  tff(c_183, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_90, c_182])).
% 3.26/1.51  tff(c_208, plain, (![B_140, A_141]: (~v1_subset_1(B_140, A_141) | v1_xboole_0(B_140) | ~m1_subset_1(B_140, k1_zfmisc_1(A_141)) | ~v1_zfmisc_1(A_141) | v1_xboole_0(A_141))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.26/1.51  tff(c_211, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_183, c_208])).
% 3.26/1.51  tff(c_217, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_129, c_211])).
% 3.26/1.51  tff(c_218, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_90, c_217])).
% 3.26/1.51  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.51  tff(c_223, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_218, c_2])).
% 3.26/1.51  tff(c_6, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.51  tff(c_8, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.51  tff(c_10, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.51  tff(c_12, plain, (![A_9, B_10, C_11, D_12]: (k3_enumset1(A_9, A_9, B_10, C_11, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.51  tff(c_14, plain, (![E_17, A_13, B_14, C_15, D_16]: (k4_enumset1(A_13, A_13, B_14, C_15, D_16, E_17)=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.51  tff(c_16, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, D_21, E_22, F_23)=k4_enumset1(A_18, B_19, C_20, D_21, E_22, F_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.51  tff(c_347, plain, (![D_227, F_225, G_221, C_222, E_224, A_226, B_223]: (k6_enumset1(A_226, A_226, B_223, C_222, D_227, E_224, F_225, G_221)=k5_enumset1(A_226, B_223, C_222, D_227, E_224, F_225, G_221))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.51  tff(c_32, plain, (![A_31, B_32, H_38, F_36, E_35, G_37, D_34, J_42]: (r2_hidden(J_42, k6_enumset1(A_31, B_32, J_42, D_34, E_35, F_36, G_37, H_38)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.26/1.51  tff(c_404, plain, (![D_231, A_234, B_233, F_228, E_229, C_232, G_230]: (r2_hidden(B_233, k5_enumset1(A_234, B_233, C_232, D_231, E_229, F_228, G_230)))), inference(superposition, [status(thm), theory('equality')], [c_347, c_32])).
% 3.26/1.51  tff(c_412, plain, (![A_235, B_240, D_239, C_236, F_238, E_237]: (r2_hidden(A_235, k4_enumset1(A_235, B_240, C_236, D_239, E_237, F_238)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_404])).
% 3.26/1.51  tff(c_420, plain, (![A_244, C_245, E_243, B_242, D_241]: (r2_hidden(A_244, k3_enumset1(A_244, B_242, C_245, D_241, E_243)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_412])).
% 3.26/1.51  tff(c_472, plain, (![A_255, B_256, C_257, D_258]: (r2_hidden(A_255, k2_enumset1(A_255, B_256, C_257, D_258)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_420])).
% 3.26/1.51  tff(c_480, plain, (![A_259, B_260, C_261]: (r2_hidden(A_259, k1_enumset1(A_259, B_260, C_261)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_472])).
% 3.26/1.51  tff(c_488, plain, (![A_262, B_263]: (r2_hidden(A_262, k2_tarski(A_262, B_263)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_480])).
% 3.26/1.51  tff(c_497, plain, (![A_273]: (r2_hidden(A_273, k1_tarski(A_273)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_488])).
% 3.26/1.51  tff(c_503, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_223, c_497])).
% 3.26/1.51  tff(c_76, plain, (![B_47, A_46]: (~r1_tarski(B_47, A_46) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.26/1.51  tff(c_507, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_503, c_76])).
% 3.26/1.51  tff(c_511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_507])).
% 3.26/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.51  
% 3.26/1.51  Inference rules
% 3.26/1.51  ----------------------
% 3.26/1.51  #Ref     : 0
% 3.26/1.51  #Sup     : 93
% 3.26/1.51  #Fact    : 0
% 3.26/1.51  #Define  : 0
% 3.26/1.51  #Split   : 1
% 3.26/1.51  #Chain   : 0
% 3.26/1.51  #Close   : 0
% 3.26/1.51  
% 3.26/1.51  Ordering : KBO
% 3.26/1.51  
% 3.26/1.51  Simplification rules
% 3.26/1.51  ----------------------
% 3.26/1.51  #Subsume      : 3
% 3.26/1.51  #Demod        : 36
% 3.26/1.51  #Tautology    : 41
% 3.26/1.51  #SimpNegUnit  : 8
% 3.26/1.51  #BackRed      : 7
% 3.26/1.51  
% 3.26/1.51  #Partial instantiations: 0
% 3.26/1.51  #Strategies tried      : 1
% 3.26/1.51  
% 3.26/1.51  Timing (in seconds)
% 3.26/1.51  ----------------------
% 3.26/1.51  Preprocessing        : 0.38
% 3.26/1.51  Parsing              : 0.19
% 3.26/1.51  CNF conversion       : 0.03
% 3.26/1.51  Main loop            : 0.30
% 3.26/1.51  Inferencing          : 0.09
% 3.26/1.51  Reduction            : 0.08
% 3.26/1.51  Demodulation         : 0.05
% 3.26/1.51  BG Simplification    : 0.03
% 3.26/1.51  Subsumption          : 0.09
% 3.26/1.51  Abstraction          : 0.02
% 3.26/1.51  MUC search           : 0.00
% 3.26/1.51  Cooper               : 0.00
% 3.26/1.51  Total                : 0.72
% 3.26/1.51  Index Insertion      : 0.00
% 3.26/1.51  Index Deletion       : 0.00
% 3.26/1.51  Index Matching       : 0.00
% 3.26/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
