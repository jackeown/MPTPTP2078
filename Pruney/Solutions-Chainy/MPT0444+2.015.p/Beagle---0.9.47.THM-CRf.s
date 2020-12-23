%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:22 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 114 expanded)
%              Number of leaves         :   38 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 181 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

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

tff(f_85,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

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

tff(c_294,plain,(
    ! [D_177,B_178,C_181,G_183,F_180,A_179,E_182] : k6_enumset1(A_179,A_179,B_178,C_181,D_177,E_182,F_180,G_183) = k5_enumset1(A_179,B_178,C_181,D_177,E_182,F_180,G_183) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [D_36,G_39,J_44,F_38,E_37,A_33,B_34,C_35] : r2_hidden(J_44,k6_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,G_39,J_44)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_431,plain,(
    ! [F_231,C_233,A_230,D_234,E_232,G_229,B_235] : r2_hidden(G_229,k5_enumset1(A_230,B_235,C_233,D_234,E_232,F_231,G_229)) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_20])).

tff(c_438,plain,(
    ! [B_237,E_239,D_238,C_236,A_240,F_241] : r2_hidden(F_241,k4_enumset1(A_240,B_237,C_236,D_238,E_239,F_241)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_431])).

tff(c_445,plain,(
    ! [A_246,E_245,D_243,B_244,C_242] : r2_hidden(E_245,k3_enumset1(A_246,B_244,C_242,D_243,E_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_438])).

tff(c_458,plain,(
    ! [D_249,A_250,B_251,C_252] : r2_hidden(D_249,k2_enumset1(A_250,B_251,C_252,D_249)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_445])).

tff(c_465,plain,(
    ! [C_253,A_254,B_255] : r2_hidden(C_253,k1_enumset1(A_254,B_255,C_253)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_458])).

tff(c_472,plain,(
    ! [B_256,A_257] : r2_hidden(B_256,k2_tarski(A_257,B_256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_465])).

tff(c_108,plain,(
    ! [A_68,B_69] : k1_setfam_1(k2_tarski(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_78,plain,(
    ! [B_50,A_49] :
      ( r1_tarski(k1_setfam_1(B_50),A_49)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_114,plain,(
    ! [A_68,B_69,A_49] :
      ( r1_tarski(k3_xboole_0(A_68,B_69),A_49)
      | ~ r2_hidden(A_49,k2_tarski(A_68,B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_78])).

tff(c_488,plain,(
    ! [A_257,B_256] : r1_tarski(k3_xboole_0(A_257,B_256),B_256) ),
    inference(resolution,[status(thm)],[c_472,c_114])).

tff(c_90,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_120,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_125,plain,(
    ! [A_72,B_73] :
      ( v1_relat_1(A_72)
      | ~ v1_relat_1(B_73)
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_76,c_120])).

tff(c_133,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k3_xboole_0(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_125])).

tff(c_88,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_82,plain,(
    ! [A_54,B_56] :
      ( r1_tarski(k2_relat_1(A_54),k2_relat_1(B_56))
      | ~ r1_tarski(A_54,B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_170,plain,(
    ! [A_132,B_133,C_134] :
      ( r1_tarski(A_132,k3_xboole_0(B_133,C_134))
      | ~ r1_tarski(A_132,C_134)
      | ~ r1_tarski(A_132,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_178,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_170,c_86])).

tff(c_219,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_222,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_219])).

tff(c_225,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2,c_222])).

tff(c_228,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_225])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_228])).

tff(c_233,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_237,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_233])).

tff(c_240,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_237])).

tff(c_255,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_258,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_255])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_258])).

tff(c_263,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.45  
% 3.20/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.45  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.20/1.45  
% 3.20/1.45  %Foreground sorts:
% 3.20/1.45  
% 3.20/1.45  
% 3.20/1.45  %Background operators:
% 3.20/1.45  
% 3.20/1.45  
% 3.20/1.45  %Foreground operators:
% 3.20/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.20/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.20/1.45  
% 3.26/1.47  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.26/1.47  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.26/1.47  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.26/1.47  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.26/1.47  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.26/1.47  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.26/1.47  tff(f_75, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.26/1.47  tff(f_77, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.26/1.47  tff(f_85, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.26/1.47  tff(f_111, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 3.26/1.47  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.26/1.47  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.26/1.47  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.26/1.47  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.26/1.47  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.26/1.47  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.47  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.47  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.47  tff(c_12, plain, (![B_16, A_15, D_18, E_19, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, E_19)=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.47  tff(c_14, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (k5_enumset1(A_20, A_20, B_21, C_22, D_23, E_24, F_25)=k4_enumset1(A_20, B_21, C_22, D_23, E_24, F_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.47  tff(c_294, plain, (![D_177, B_178, C_181, G_183, F_180, A_179, E_182]: (k6_enumset1(A_179, A_179, B_178, C_181, D_177, E_182, F_180, G_183)=k5_enumset1(A_179, B_178, C_181, D_177, E_182, F_180, G_183))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.47  tff(c_20, plain, (![D_36, G_39, J_44, F_38, E_37, A_33, B_34, C_35]: (r2_hidden(J_44, k6_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, G_39, J_44)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.26/1.47  tff(c_431, plain, (![F_231, C_233, A_230, D_234, E_232, G_229, B_235]: (r2_hidden(G_229, k5_enumset1(A_230, B_235, C_233, D_234, E_232, F_231, G_229)))), inference(superposition, [status(thm), theory('equality')], [c_294, c_20])).
% 3.26/1.47  tff(c_438, plain, (![B_237, E_239, D_238, C_236, A_240, F_241]: (r2_hidden(F_241, k4_enumset1(A_240, B_237, C_236, D_238, E_239, F_241)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_431])).
% 3.26/1.47  tff(c_445, plain, (![A_246, E_245, D_243, B_244, C_242]: (r2_hidden(E_245, k3_enumset1(A_246, B_244, C_242, D_243, E_245)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_438])).
% 3.26/1.47  tff(c_458, plain, (![D_249, A_250, B_251, C_252]: (r2_hidden(D_249, k2_enumset1(A_250, B_251, C_252, D_249)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_445])).
% 3.26/1.47  tff(c_465, plain, (![C_253, A_254, B_255]: (r2_hidden(C_253, k1_enumset1(A_254, B_255, C_253)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_458])).
% 3.26/1.47  tff(c_472, plain, (![B_256, A_257]: (r2_hidden(B_256, k2_tarski(A_257, B_256)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_465])).
% 3.26/1.47  tff(c_108, plain, (![A_68, B_69]: (k1_setfam_1(k2_tarski(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.47  tff(c_78, plain, (![B_50, A_49]: (r1_tarski(k1_setfam_1(B_50), A_49) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.26/1.47  tff(c_114, plain, (![A_68, B_69, A_49]: (r1_tarski(k3_xboole_0(A_68, B_69), A_49) | ~r2_hidden(A_49, k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_78])).
% 3.26/1.47  tff(c_488, plain, (![A_257, B_256]: (r1_tarski(k3_xboole_0(A_257, B_256), B_256))), inference(resolution, [status(thm)], [c_472, c_114])).
% 3.26/1.47  tff(c_90, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.26/1.47  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.47  tff(c_76, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.26/1.47  tff(c_120, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.26/1.47  tff(c_125, plain, (![A_72, B_73]: (v1_relat_1(A_72) | ~v1_relat_1(B_73) | ~r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_76, c_120])).
% 3.26/1.47  tff(c_133, plain, (![A_1, B_2]: (v1_relat_1(k3_xboole_0(A_1, B_2)) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_125])).
% 3.26/1.47  tff(c_88, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.26/1.47  tff(c_82, plain, (![A_54, B_56]: (r1_tarski(k2_relat_1(A_54), k2_relat_1(B_56)) | ~r1_tarski(A_54, B_56) | ~v1_relat_1(B_56) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.26/1.47  tff(c_170, plain, (![A_132, B_133, C_134]: (r1_tarski(A_132, k3_xboole_0(B_133, C_134)) | ~r1_tarski(A_132, C_134) | ~r1_tarski(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.47  tff(c_86, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.26/1.47  tff(c_178, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_170, c_86])).
% 3.26/1.47  tff(c_219, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_178])).
% 3.26/1.47  tff(c_222, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_219])).
% 3.26/1.47  tff(c_225, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2, c_222])).
% 3.26/1.47  tff(c_228, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_133, c_225])).
% 3.26/1.47  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_228])).
% 3.26/1.47  tff(c_233, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_178])).
% 3.26/1.47  tff(c_237, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_233])).
% 3.26/1.47  tff(c_240, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_237])).
% 3.26/1.47  tff(c_255, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_240])).
% 3.26/1.47  tff(c_258, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_133, c_255])).
% 3.26/1.47  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_258])).
% 3.26/1.47  tff(c_263, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_240])).
% 3.26/1.47  tff(c_493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_488, c_263])).
% 3.26/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.47  
% 3.26/1.47  Inference rules
% 3.26/1.47  ----------------------
% 3.26/1.47  #Ref     : 0
% 3.26/1.47  #Sup     : 90
% 3.26/1.47  #Fact    : 0
% 3.26/1.47  #Define  : 0
% 3.26/1.47  #Split   : 3
% 3.26/1.47  #Chain   : 0
% 3.26/1.47  #Close   : 0
% 3.26/1.47  
% 3.26/1.47  Ordering : KBO
% 3.26/1.47  
% 3.26/1.47  Simplification rules
% 3.26/1.47  ----------------------
% 3.26/1.47  #Subsume      : 5
% 3.26/1.47  #Demod        : 11
% 3.26/1.47  #Tautology    : 24
% 3.26/1.47  #SimpNegUnit  : 0
% 3.26/1.47  #BackRed      : 1
% 3.26/1.47  
% 3.26/1.47  #Partial instantiations: 0
% 3.26/1.47  #Strategies tried      : 1
% 3.26/1.47  
% 3.26/1.47  Timing (in seconds)
% 3.26/1.47  ----------------------
% 3.26/1.47  Preprocessing        : 0.37
% 3.26/1.47  Parsing              : 0.18
% 3.26/1.47  CNF conversion       : 0.03
% 3.26/1.47  Main loop            : 0.33
% 3.26/1.47  Inferencing          : 0.10
% 3.26/1.47  Reduction            : 0.09
% 3.26/1.47  Demodulation         : 0.06
% 3.26/1.47  BG Simplification    : 0.03
% 3.26/1.47  Subsumption          : 0.10
% 3.26/1.47  Abstraction          : 0.03
% 3.26/1.47  MUC search           : 0.00
% 3.26/1.47  Cooper               : 0.00
% 3.26/1.47  Total                : 0.73
% 3.26/1.47  Index Insertion      : 0.00
% 3.26/1.47  Index Deletion       : 0.00
% 3.26/1.47  Index Matching       : 0.00
% 3.26/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
