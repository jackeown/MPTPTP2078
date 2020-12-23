%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:38 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 113 expanded)
%              Number of leaves         :   37 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 178 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

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

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

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

tff(c_288,plain,(
    ! [D_177,B_178,C_181,G_183,F_180,A_179,E_182] : k6_enumset1(A_179,A_179,B_178,C_181,D_177,E_182,F_180,G_183) = k5_enumset1(A_179,B_178,C_181,D_177,E_182,F_180,G_183) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [D_36,G_39,J_44,F_38,E_37,A_33,B_34,C_35] : r2_hidden(J_44,k6_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,G_39,J_44)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_321,plain,(
    ! [G_184,A_185,C_188,B_190,D_189,E_187,F_186] : r2_hidden(G_184,k5_enumset1(A_185,B_190,C_188,D_189,E_187,F_186,G_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_20])).

tff(c_328,plain,(
    ! [A_195,F_196,B_192,D_193,E_194,C_191] : r2_hidden(F_196,k4_enumset1(A_195,B_192,C_191,D_193,E_194,F_196)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_321])).

tff(c_335,plain,(
    ! [B_199,E_200,C_197,D_198,A_201] : r2_hidden(E_200,k3_enumset1(A_201,B_199,C_197,D_198,E_200)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_328])).

tff(c_343,plain,(
    ! [D_204,A_205,B_206,C_207] : r2_hidden(D_204,k2_enumset1(A_205,B_206,C_207,D_204)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_335])).

tff(c_350,plain,(
    ! [C_208,A_209,B_210] : r2_hidden(C_208,k1_enumset1(A_209,B_210,C_208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_343])).

tff(c_357,plain,(
    ! [B_211,A_212] : r2_hidden(B_211,k2_tarski(A_212,B_211)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_350])).

tff(c_72,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_114,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(k1_setfam_1(B_68),A_69)
      | ~ r2_hidden(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_117,plain,(
    ! [A_45,B_46,A_69] :
      ( r1_tarski(k3_xboole_0(A_45,B_46),A_69)
      | ~ r2_hidden(A_69,k2_tarski(A_45,B_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_114])).

tff(c_368,plain,(
    ! [A_212,B_211] : r1_tarski(k3_xboole_0(A_212,B_211),B_211) ),
    inference(resolution,[status(thm)],[c_357,c_117])).

tff(c_88,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_118,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_123,plain,(
    ! [A_72,B_73] :
      ( v1_relat_1(A_72)
      | ~ v1_relat_1(B_73)
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_76,c_118])).

tff(c_131,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k3_xboole_0(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_123])).

tff(c_86,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_82,plain,(
    ! [A_54,B_56] :
      ( r1_tarski(k3_relat_1(A_54),k3_relat_1(B_56))
      | ~ r1_tarski(A_54,B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_185,plain,(
    ! [A_152,B_153,C_154] :
      ( r1_tarski(A_152,k3_xboole_0(B_153,C_154))
      | ~ r1_tarski(A_152,C_154)
      | ~ r1_tarski(A_152,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_193,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_185,c_84])).

tff(c_213,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_216,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_213])).

tff(c_219,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2,c_216])).

tff(c_222,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_219])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_222])).

tff(c_227,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_231,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_227])).

tff(c_234,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_231])).

tff(c_249,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_252,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_249])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_252])).

tff(c_257,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.44  
% 3.05/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.05/1.44  
% 3.05/1.44  %Foreground sorts:
% 3.05/1.44  
% 3.05/1.44  
% 3.05/1.44  %Background operators:
% 3.05/1.44  
% 3.05/1.44  
% 3.05/1.44  %Foreground operators:
% 3.05/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.05/1.44  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.05/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.05/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.05/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.05/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.05/1.44  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.05/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.05/1.44  
% 3.05/1.46  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.05/1.46  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.05/1.46  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.05/1.46  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.05/1.46  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.05/1.46  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.05/1.46  tff(f_75, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.05/1.46  tff(f_77, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.05/1.46  tff(f_85, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.05/1.46  tff(f_109, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 3.05/1.46  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.05/1.46  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.05/1.46  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.05/1.46  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 3.05/1.46  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.05/1.46  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.46  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.05/1.46  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.05/1.46  tff(c_12, plain, (![B_16, A_15, D_18, E_19, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, E_19)=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.05/1.46  tff(c_14, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (k5_enumset1(A_20, A_20, B_21, C_22, D_23, E_24, F_25)=k4_enumset1(A_20, B_21, C_22, D_23, E_24, F_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.46  tff(c_288, plain, (![D_177, B_178, C_181, G_183, F_180, A_179, E_182]: (k6_enumset1(A_179, A_179, B_178, C_181, D_177, E_182, F_180, G_183)=k5_enumset1(A_179, B_178, C_181, D_177, E_182, F_180, G_183))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.05/1.46  tff(c_20, plain, (![D_36, G_39, J_44, F_38, E_37, A_33, B_34, C_35]: (r2_hidden(J_44, k6_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, G_39, J_44)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.05/1.46  tff(c_321, plain, (![G_184, A_185, C_188, B_190, D_189, E_187, F_186]: (r2_hidden(G_184, k5_enumset1(A_185, B_190, C_188, D_189, E_187, F_186, G_184)))), inference(superposition, [status(thm), theory('equality')], [c_288, c_20])).
% 3.05/1.46  tff(c_328, plain, (![A_195, F_196, B_192, D_193, E_194, C_191]: (r2_hidden(F_196, k4_enumset1(A_195, B_192, C_191, D_193, E_194, F_196)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_321])).
% 3.05/1.46  tff(c_335, plain, (![B_199, E_200, C_197, D_198, A_201]: (r2_hidden(E_200, k3_enumset1(A_201, B_199, C_197, D_198, E_200)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_328])).
% 3.05/1.46  tff(c_343, plain, (![D_204, A_205, B_206, C_207]: (r2_hidden(D_204, k2_enumset1(A_205, B_206, C_207, D_204)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_335])).
% 3.05/1.46  tff(c_350, plain, (![C_208, A_209, B_210]: (r2_hidden(C_208, k1_enumset1(A_209, B_210, C_208)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_343])).
% 3.05/1.46  tff(c_357, plain, (![B_211, A_212]: (r2_hidden(B_211, k2_tarski(A_212, B_211)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_350])).
% 3.05/1.46  tff(c_72, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.05/1.46  tff(c_114, plain, (![B_68, A_69]: (r1_tarski(k1_setfam_1(B_68), A_69) | ~r2_hidden(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.05/1.46  tff(c_117, plain, (![A_45, B_46, A_69]: (r1_tarski(k3_xboole_0(A_45, B_46), A_69) | ~r2_hidden(A_69, k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_114])).
% 3.05/1.46  tff(c_368, plain, (![A_212, B_211]: (r1_tarski(k3_xboole_0(A_212, B_211), B_211))), inference(resolution, [status(thm)], [c_357, c_117])).
% 3.05/1.46  tff(c_88, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.05/1.46  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.46  tff(c_76, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.05/1.46  tff(c_118, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.05/1.46  tff(c_123, plain, (![A_72, B_73]: (v1_relat_1(A_72) | ~v1_relat_1(B_73) | ~r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_76, c_118])).
% 3.05/1.46  tff(c_131, plain, (![A_1, B_2]: (v1_relat_1(k3_xboole_0(A_1, B_2)) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_123])).
% 3.05/1.46  tff(c_86, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.05/1.46  tff(c_82, plain, (![A_54, B_56]: (r1_tarski(k3_relat_1(A_54), k3_relat_1(B_56)) | ~r1_tarski(A_54, B_56) | ~v1_relat_1(B_56) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.05/1.46  tff(c_185, plain, (![A_152, B_153, C_154]: (r1_tarski(A_152, k3_xboole_0(B_153, C_154)) | ~r1_tarski(A_152, C_154) | ~r1_tarski(A_152, B_153))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.46  tff(c_84, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.05/1.46  tff(c_193, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_185, c_84])).
% 3.05/1.46  tff(c_213, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_193])).
% 3.05/1.46  tff(c_216, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_213])).
% 3.05/1.46  tff(c_219, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2, c_216])).
% 3.05/1.46  tff(c_222, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_131, c_219])).
% 3.05/1.46  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_222])).
% 3.05/1.46  tff(c_227, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_193])).
% 3.05/1.46  tff(c_231, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_227])).
% 3.05/1.46  tff(c_234, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_231])).
% 3.05/1.46  tff(c_249, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_234])).
% 3.05/1.46  tff(c_252, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_131, c_249])).
% 3.05/1.46  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_252])).
% 3.05/1.46  tff(c_257, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_234])).
% 3.05/1.46  tff(c_373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_368, c_257])).
% 3.05/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.46  
% 3.05/1.46  Inference rules
% 3.05/1.46  ----------------------
% 3.05/1.46  #Ref     : 0
% 3.05/1.46  #Sup     : 63
% 3.05/1.46  #Fact    : 0
% 3.05/1.46  #Define  : 0
% 3.05/1.46  #Split   : 3
% 3.05/1.46  #Chain   : 0
% 3.05/1.46  #Close   : 0
% 3.05/1.46  
% 3.05/1.46  Ordering : KBO
% 3.05/1.46  
% 3.05/1.46  Simplification rules
% 3.05/1.46  ----------------------
% 3.05/1.46  #Subsume      : 1
% 3.05/1.46  #Demod        : 8
% 3.05/1.46  #Tautology    : 15
% 3.05/1.46  #SimpNegUnit  : 0
% 3.05/1.46  #BackRed      : 1
% 3.05/1.46  
% 3.05/1.46  #Partial instantiations: 0
% 3.05/1.46  #Strategies tried      : 1
% 3.05/1.46  
% 3.05/1.46  Timing (in seconds)
% 3.05/1.46  ----------------------
% 3.05/1.46  Preprocessing        : 0.37
% 3.05/1.46  Parsing              : 0.18
% 3.05/1.46  CNF conversion       : 0.03
% 3.05/1.46  Main loop            : 0.27
% 3.05/1.46  Inferencing          : 0.08
% 3.05/1.46  Reduction            : 0.07
% 3.05/1.46  Demodulation         : 0.05
% 3.05/1.46  BG Simplification    : 0.02
% 3.05/1.46  Subsumption          : 0.09
% 3.05/1.46  Abstraction          : 0.02
% 3.05/1.46  MUC search           : 0.00
% 3.05/1.46  Cooper               : 0.00
% 3.05/1.46  Total                : 0.68
% 3.05/1.46  Index Insertion      : 0.00
% 3.05/1.46  Index Deletion       : 0.00
% 3.05/1.46  Index Matching       : 0.00
% 3.05/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
