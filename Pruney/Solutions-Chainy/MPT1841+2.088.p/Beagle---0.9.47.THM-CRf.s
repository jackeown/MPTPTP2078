%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:39 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   77 (  94 expanded)
%              Number of leaves         :   39 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 139 expanded)
%              Number of equality atoms :   34 (  38 expanded)
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

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_82,axiom,(
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

tff(c_20,plain,(
    ! [A_30] : k2_zfmisc_1(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,(
    ! [A_61,B_62] : ~ r2_hidden(A_61,k2_zfmisc_1(A_61,B_62)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_130,plain,(
    ! [A_30] : ~ r2_hidden(A_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_88,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_92,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_165,plain,(
    ! [A_73,B_74] :
      ( k6_domain_1(A_73,B_74) = k1_tarski(B_74)
      | ~ m1_subset_1(B_74,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_168,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_165])).

tff(c_171,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_168])).

tff(c_90,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_172,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_90])).

tff(c_192,plain,(
    ! [A_127,B_128] :
      ( m1_subset_1(k6_domain_1(A_127,B_128),k1_zfmisc_1(A_127))
      | ~ m1_subset_1(B_128,A_127)
      | v1_xboole_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_201,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_192])).

tff(c_205,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_201])).

tff(c_206,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_205])).

tff(c_475,plain,(
    ! [B_211,A_212] :
      ( ~ v1_subset_1(B_211,A_212)
      | v1_xboole_0(B_211)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(A_212))
      | ~ v1_zfmisc_1(A_212)
      | v1_xboole_0(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_481,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_206,c_475])).

tff(c_490,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_172,c_481])).

tff(c_491,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_490])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_496,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_491,c_2])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10,D_11] : k3_enumset1(A_8,A_8,B_9,C_10,D_11) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [E_16,D_15,C_14,A_12,B_13] : k4_enumset1(A_12,A_12,B_13,C_14,D_15,E_16) = k3_enumset1(A_12,B_13,C_14,D_15,E_16) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] : k5_enumset1(A_17,A_17,B_18,C_19,D_20,E_21,F_22) = k4_enumset1(A_17,B_18,C_19,D_20,E_21,F_22) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_600,plain,(
    ! [G_221,A_225,F_220,E_222,D_224,B_223,C_219] : k6_enumset1(A_225,A_225,B_223,C_219,D_224,E_222,F_220,G_221) = k5_enumset1(A_225,B_223,C_219,D_224,E_222,F_220,G_221) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [H_41,D_37,J_45,A_34,F_39,B_35,C_36,E_38] : r2_hidden(J_45,k6_enumset1(A_34,B_35,C_36,D_37,E_38,F_39,J_45,H_41)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_638,plain,(
    ! [E_227,A_230,C_228,D_232,B_231,G_229,F_226] : r2_hidden(F_226,k5_enumset1(A_230,B_231,C_228,D_232,E_227,F_226,G_229)) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_30])).

tff(c_642,plain,(
    ! [C_233,F_236,E_238,A_234,D_237,B_235] : r2_hidden(E_238,k4_enumset1(A_234,B_235,C_233,D_237,E_238,F_236)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_638])).

tff(c_657,plain,(
    ! [C_244,A_241,B_240,D_243,E_242] : r2_hidden(D_243,k3_enumset1(A_241,B_240,C_244,D_243,E_242)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_642])).

tff(c_661,plain,(
    ! [C_245,A_246,B_247,D_248] : r2_hidden(C_245,k2_enumset1(A_246,B_247,C_245,D_248)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_657])).

tff(c_665,plain,(
    ! [B_249,A_250,C_251] : r2_hidden(B_249,k1_enumset1(A_250,B_249,C_251)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_661])).

tff(c_669,plain,(
    ! [A_252,B_253] : r2_hidden(A_252,k2_tarski(A_252,B_253)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_665])).

tff(c_673,plain,(
    ! [A_254] : r2_hidden(A_254,k1_tarski(A_254)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_669])).

tff(c_676,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_673])).

tff(c_678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.48  
% 3.23/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.48  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.23/1.48  
% 3.23/1.48  %Foreground sorts:
% 3.23/1.48  
% 3.23/1.48  
% 3.23/1.48  %Background operators:
% 3.23/1.48  
% 3.23/1.48  
% 3.23/1.48  %Foreground operators:
% 3.23/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.48  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.23/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.23/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.48  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.23/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.48  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.23/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.48  
% 3.36/1.49  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.36/1.49  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.36/1.49  tff(f_130, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.36/1.49  tff(f_104, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.36/1.49  tff(f_97, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.36/1.49  tff(f_118, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.36/1.49  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.36/1.49  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.36/1.49  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.36/1.49  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.36/1.49  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.36/1.49  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.36/1.49  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.36/1.49  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.36/1.49  tff(f_82, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.36/1.49  tff(c_20, plain, (![A_30]: (k2_zfmisc_1(A_30, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.49  tff(c_127, plain, (![A_61, B_62]: (~r2_hidden(A_61, k2_zfmisc_1(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.36/1.49  tff(c_130, plain, (![A_30]: (~r2_hidden(A_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_127])).
% 3.36/1.49  tff(c_94, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.36/1.49  tff(c_88, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.36/1.49  tff(c_92, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.36/1.49  tff(c_165, plain, (![A_73, B_74]: (k6_domain_1(A_73, B_74)=k1_tarski(B_74) | ~m1_subset_1(B_74, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.36/1.49  tff(c_168, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_92, c_165])).
% 3.36/1.49  tff(c_171, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_94, c_168])).
% 3.36/1.49  tff(c_90, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.36/1.49  tff(c_172, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_90])).
% 3.36/1.49  tff(c_192, plain, (![A_127, B_128]: (m1_subset_1(k6_domain_1(A_127, B_128), k1_zfmisc_1(A_127)) | ~m1_subset_1(B_128, A_127) | v1_xboole_0(A_127))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.36/1.49  tff(c_201, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_171, c_192])).
% 3.36/1.49  tff(c_205, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_201])).
% 3.36/1.49  tff(c_206, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_94, c_205])).
% 3.36/1.49  tff(c_475, plain, (![B_211, A_212]: (~v1_subset_1(B_211, A_212) | v1_xboole_0(B_211) | ~m1_subset_1(B_211, k1_zfmisc_1(A_212)) | ~v1_zfmisc_1(A_212) | v1_xboole_0(A_212))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.36/1.49  tff(c_481, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_206, c_475])).
% 3.36/1.49  tff(c_490, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_172, c_481])).
% 3.36/1.49  tff(c_491, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_94, c_490])).
% 3.36/1.49  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.49  tff(c_496, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_491, c_2])).
% 3.36/1.49  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.49  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.49  tff(c_8, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.49  tff(c_10, plain, (![A_8, B_9, C_10, D_11]: (k3_enumset1(A_8, A_8, B_9, C_10, D_11)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.36/1.49  tff(c_12, plain, (![E_16, D_15, C_14, A_12, B_13]: (k4_enumset1(A_12, A_12, B_13, C_14, D_15, E_16)=k3_enumset1(A_12, B_13, C_14, D_15, E_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.49  tff(c_14, plain, (![E_21, D_20, C_19, B_18, A_17, F_22]: (k5_enumset1(A_17, A_17, B_18, C_19, D_20, E_21, F_22)=k4_enumset1(A_17, B_18, C_19, D_20, E_21, F_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.36/1.49  tff(c_600, plain, (![G_221, A_225, F_220, E_222, D_224, B_223, C_219]: (k6_enumset1(A_225, A_225, B_223, C_219, D_224, E_222, F_220, G_221)=k5_enumset1(A_225, B_223, C_219, D_224, E_222, F_220, G_221))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.49  tff(c_30, plain, (![H_41, D_37, J_45, A_34, F_39, B_35, C_36, E_38]: (r2_hidden(J_45, k6_enumset1(A_34, B_35, C_36, D_37, E_38, F_39, J_45, H_41)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.36/1.49  tff(c_638, plain, (![E_227, A_230, C_228, D_232, B_231, G_229, F_226]: (r2_hidden(F_226, k5_enumset1(A_230, B_231, C_228, D_232, E_227, F_226, G_229)))), inference(superposition, [status(thm), theory('equality')], [c_600, c_30])).
% 3.36/1.49  tff(c_642, plain, (![C_233, F_236, E_238, A_234, D_237, B_235]: (r2_hidden(E_238, k4_enumset1(A_234, B_235, C_233, D_237, E_238, F_236)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_638])).
% 3.36/1.49  tff(c_657, plain, (![C_244, A_241, B_240, D_243, E_242]: (r2_hidden(D_243, k3_enumset1(A_241, B_240, C_244, D_243, E_242)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_642])).
% 3.36/1.49  tff(c_661, plain, (![C_245, A_246, B_247, D_248]: (r2_hidden(C_245, k2_enumset1(A_246, B_247, C_245, D_248)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_657])).
% 3.36/1.49  tff(c_665, plain, (![B_249, A_250, C_251]: (r2_hidden(B_249, k1_enumset1(A_250, B_249, C_251)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_661])).
% 3.36/1.49  tff(c_669, plain, (![A_252, B_253]: (r2_hidden(A_252, k2_tarski(A_252, B_253)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_665])).
% 3.36/1.49  tff(c_673, plain, (![A_254]: (r2_hidden(A_254, k1_tarski(A_254)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_669])).
% 3.36/1.49  tff(c_676, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_496, c_673])).
% 3.36/1.49  tff(c_678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_676])).
% 3.36/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.49  
% 3.36/1.49  Inference rules
% 3.36/1.49  ----------------------
% 3.36/1.49  #Ref     : 0
% 3.36/1.49  #Sup     : 132
% 3.36/1.49  #Fact    : 0
% 3.36/1.49  #Define  : 0
% 3.36/1.49  #Split   : 3
% 3.36/1.49  #Chain   : 0
% 3.36/1.49  #Close   : 0
% 3.36/1.49  
% 3.36/1.49  Ordering : KBO
% 3.36/1.49  
% 3.36/1.49  Simplification rules
% 3.36/1.49  ----------------------
% 3.36/1.49  #Subsume      : 8
% 3.36/1.49  #Demod        : 54
% 3.36/1.49  #Tautology    : 74
% 3.36/1.49  #SimpNegUnit  : 18
% 3.36/1.49  #BackRed      : 15
% 3.36/1.49  
% 3.36/1.49  #Partial instantiations: 0
% 3.36/1.49  #Strategies tried      : 1
% 3.36/1.49  
% 3.36/1.49  Timing (in seconds)
% 3.36/1.49  ----------------------
% 3.36/1.50  Preprocessing        : 0.35
% 3.36/1.50  Parsing              : 0.16
% 3.36/1.50  CNF conversion       : 0.03
% 3.36/1.50  Main loop            : 0.33
% 3.36/1.50  Inferencing          : 0.11
% 3.36/1.50  Reduction            : 0.10
% 3.36/1.50  Demodulation         : 0.06
% 3.36/1.50  BG Simplification    : 0.03
% 3.36/1.50  Subsumption          : 0.09
% 3.36/1.50  Abstraction          : 0.02
% 3.36/1.50  MUC search           : 0.00
% 3.36/1.50  Cooper               : 0.00
% 3.36/1.50  Total                : 0.72
% 3.36/1.50  Index Insertion      : 0.00
% 3.36/1.50  Index Deletion       : 0.00
% 3.36/1.50  Index Matching       : 0.00
% 3.36/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
