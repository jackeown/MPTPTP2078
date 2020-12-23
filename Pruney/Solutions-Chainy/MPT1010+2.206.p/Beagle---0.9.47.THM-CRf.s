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
% DateTime   : Thu Dec  3 10:15:32 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   75 (  91 expanded)
%              Number of leaves         :   42 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 164 expanded)
%              Number of equality atoms :   77 (  93 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_74,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(c_72,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [A_44] : k1_setfam_1(k1_tarski(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_57,B_58] : k1_setfam_1(k2_tarski(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_125,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_116])).

tff(c_128,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_125])).

tff(c_138,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_147,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k4_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_138])).

tff(c_150,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_147])).

tff(c_20,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_151,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_20])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_74,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_328,plain,(
    ! [D_175,C_176,B_177,A_178] :
      ( r2_hidden(k1_funct_1(D_175,C_176),B_177)
      | k1_xboole_0 = B_177
      | ~ r2_hidden(C_176,A_178)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177)))
      | ~ v1_funct_2(D_175,A_178,B_177)
      | ~ v1_funct_1(D_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_415,plain,(
    ! [D_200,B_201] :
      ( r2_hidden(k1_funct_1(D_200,'#skF_5'),B_201)
      | k1_xboole_0 = B_201
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_201)))
      | ~ v1_funct_2(D_200,'#skF_3',B_201)
      | ~ v1_funct_1(D_200) ) ),
    inference(resolution,[status(thm)],[c_74,c_328])).

tff(c_418,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_415])).

tff(c_421,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_418])).

tff(c_422,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_421])).

tff(c_8,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k2_enumset1(A_7,A_7,B_8,C_9) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12,D_13] : k3_enumset1(A_10,A_10,B_11,C_12,D_13) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k4_enumset1(A_14,A_14,B_15,C_16,D_17,E_18) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_281,plain,(
    ! [C_160,B_159,H_154,A_155,F_157,D_156,E_158] :
      ( H_154 = F_157
      | H_154 = E_158
      | H_154 = D_156
      | H_154 = C_160
      | H_154 = B_159
      | H_154 = A_155
      | ~ r2_hidden(H_154,k4_enumset1(A_155,B_159,C_160,D_156,E_158,F_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_426,plain,(
    ! [A_207,D_203,B_206,E_202,C_205,H_204] :
      ( H_204 = E_202
      | H_204 = D_203
      | H_204 = C_205
      | H_204 = B_206
      | H_204 = A_207
      | H_204 = A_207
      | ~ r2_hidden(H_204,k3_enumset1(A_207,B_206,C_205,D_203,E_202)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_281])).

tff(c_456,plain,(
    ! [H_211,B_210,C_214,D_213,A_212] :
      ( H_211 = D_213
      | H_211 = C_214
      | H_211 = B_210
      | H_211 = A_212
      | H_211 = A_212
      | H_211 = A_212
      | ~ r2_hidden(H_211,k2_enumset1(A_212,B_210,C_214,D_213)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_426])).

tff(c_480,plain,(
    ! [H_215,C_216,B_217,A_218] :
      ( H_215 = C_216
      | H_215 = B_217
      | H_215 = A_218
      | H_215 = A_218
      | H_215 = A_218
      | H_215 = A_218
      | ~ r2_hidden(H_215,k1_enumset1(A_218,B_217,C_216)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_456])).

tff(c_499,plain,(
    ! [H_219,B_220,A_221] :
      ( H_219 = B_220
      | H_219 = A_221
      | H_219 = A_221
      | H_219 = A_221
      | H_219 = A_221
      | H_219 = A_221
      | ~ r2_hidden(H_219,k2_tarski(A_221,B_220)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_480])).

tff(c_513,plain,(
    ! [H_222,A_223] :
      ( H_222 = A_223
      | H_222 = A_223
      | H_222 = A_223
      | H_222 = A_223
      | H_222 = A_223
      | H_222 = A_223
      | ~ r2_hidden(H_222,k1_tarski(A_223)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_499])).

tff(c_516,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_422,c_513])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_72,c_72,c_72,c_72,c_72,c_516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:49:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.41  
% 2.93/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.41  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.93/1.41  
% 2.93/1.41  %Foreground sorts:
% 2.93/1.41  
% 2.93/1.41  
% 2.93/1.41  %Background operators:
% 2.93/1.41  
% 2.93/1.41  
% 2.93/1.41  %Foreground operators:
% 2.93/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.93/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.93/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.93/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.93/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.93/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.93/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.93/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.93/1.41  
% 2.93/1.43  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.93/1.43  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.93/1.43  tff(f_74, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.93/1.43  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.93/1.43  tff(f_76, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.93/1.43  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.93/1.43  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.93/1.43  tff(f_88, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.93/1.43  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.93/1.43  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.93/1.43  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.93/1.43  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.93/1.43  tff(f_72, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 2.93/1.43  tff(c_72, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.93/1.43  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.93/1.43  tff(c_66, plain, (![A_44]: (k1_setfam_1(k1_tarski(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.93/1.43  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.43  tff(c_116, plain, (![A_57, B_58]: (k1_setfam_1(k2_tarski(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.93/1.43  tff(c_125, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_116])).
% 2.93/1.43  tff(c_128, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_125])).
% 2.93/1.43  tff(c_138, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.43  tff(c_147, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k4_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_128, c_138])).
% 2.93/1.43  tff(c_150, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_147])).
% 2.93/1.43  tff(c_20, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.93/1.43  tff(c_151, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_20])).
% 2.93/1.43  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.93/1.43  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.93/1.43  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.93/1.43  tff(c_74, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.93/1.43  tff(c_328, plain, (![D_175, C_176, B_177, A_178]: (r2_hidden(k1_funct_1(D_175, C_176), B_177) | k1_xboole_0=B_177 | ~r2_hidden(C_176, A_178) | ~m1_subset_1(D_175, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))) | ~v1_funct_2(D_175, A_178, B_177) | ~v1_funct_1(D_175))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.93/1.43  tff(c_415, plain, (![D_200, B_201]: (r2_hidden(k1_funct_1(D_200, '#skF_5'), B_201) | k1_xboole_0=B_201 | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_201))) | ~v1_funct_2(D_200, '#skF_3', B_201) | ~v1_funct_1(D_200))), inference(resolution, [status(thm)], [c_74, c_328])).
% 2.93/1.43  tff(c_418, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_415])).
% 2.93/1.43  tff(c_421, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_418])).
% 2.93/1.43  tff(c_422, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_151, c_421])).
% 2.93/1.43  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.93/1.43  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.43  tff(c_12, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.43  tff(c_14, plain, (![E_18, C_16, D_17, A_14, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, D_17, E_18)=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.43  tff(c_281, plain, (![C_160, B_159, H_154, A_155, F_157, D_156, E_158]: (H_154=F_157 | H_154=E_158 | H_154=D_156 | H_154=C_160 | H_154=B_159 | H_154=A_155 | ~r2_hidden(H_154, k4_enumset1(A_155, B_159, C_160, D_156, E_158, F_157)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.93/1.43  tff(c_426, plain, (![A_207, D_203, B_206, E_202, C_205, H_204]: (H_204=E_202 | H_204=D_203 | H_204=C_205 | H_204=B_206 | H_204=A_207 | H_204=A_207 | ~r2_hidden(H_204, k3_enumset1(A_207, B_206, C_205, D_203, E_202)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_281])).
% 2.93/1.43  tff(c_456, plain, (![H_211, B_210, C_214, D_213, A_212]: (H_211=D_213 | H_211=C_214 | H_211=B_210 | H_211=A_212 | H_211=A_212 | H_211=A_212 | ~r2_hidden(H_211, k2_enumset1(A_212, B_210, C_214, D_213)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_426])).
% 2.93/1.43  tff(c_480, plain, (![H_215, C_216, B_217, A_218]: (H_215=C_216 | H_215=B_217 | H_215=A_218 | H_215=A_218 | H_215=A_218 | H_215=A_218 | ~r2_hidden(H_215, k1_enumset1(A_218, B_217, C_216)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_456])).
% 2.93/1.43  tff(c_499, plain, (![H_219, B_220, A_221]: (H_219=B_220 | H_219=A_221 | H_219=A_221 | H_219=A_221 | H_219=A_221 | H_219=A_221 | ~r2_hidden(H_219, k2_tarski(A_221, B_220)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_480])).
% 2.93/1.43  tff(c_513, plain, (![H_222, A_223]: (H_222=A_223 | H_222=A_223 | H_222=A_223 | H_222=A_223 | H_222=A_223 | H_222=A_223 | ~r2_hidden(H_222, k1_tarski(A_223)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_499])).
% 2.93/1.43  tff(c_516, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_422, c_513])).
% 2.93/1.43  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_72, c_72, c_72, c_72, c_72, c_516])).
% 2.93/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.43  
% 2.93/1.43  Inference rules
% 2.93/1.43  ----------------------
% 2.93/1.43  #Ref     : 0
% 2.93/1.43  #Sup     : 103
% 2.93/1.43  #Fact    : 0
% 2.93/1.43  #Define  : 0
% 2.93/1.43  #Split   : 0
% 2.93/1.43  #Chain   : 0
% 2.93/1.43  #Close   : 0
% 2.93/1.43  
% 2.93/1.43  Ordering : KBO
% 2.93/1.43  
% 2.93/1.43  Simplification rules
% 2.93/1.43  ----------------------
% 2.93/1.43  #Subsume      : 0
% 2.93/1.43  #Demod        : 10
% 2.93/1.43  #Tautology    : 55
% 2.93/1.43  #SimpNegUnit  : 4
% 2.93/1.43  #BackRed      : 1
% 2.93/1.43  
% 2.93/1.43  #Partial instantiations: 0
% 2.93/1.43  #Strategies tried      : 1
% 2.93/1.43  
% 2.93/1.43  Timing (in seconds)
% 2.93/1.43  ----------------------
% 2.93/1.43  Preprocessing        : 0.36
% 2.93/1.43  Parsing              : 0.18
% 2.93/1.43  CNF conversion       : 0.03
% 2.93/1.43  Main loop            : 0.31
% 2.93/1.43  Inferencing          : 0.11
% 2.93/1.43  Reduction            : 0.10
% 2.93/1.43  Demodulation         : 0.07
% 2.93/1.43  BG Simplification    : 0.02
% 2.93/1.43  Subsumption          : 0.07
% 2.93/1.43  Abstraction          : 0.02
% 2.93/1.43  MUC search           : 0.00
% 2.93/1.43  Cooper               : 0.00
% 2.93/1.43  Total                : 0.70
% 2.93/1.43  Index Insertion      : 0.00
% 2.93/1.43  Index Deletion       : 0.00
% 2.93/1.43  Index Matching       : 0.00
% 2.93/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
