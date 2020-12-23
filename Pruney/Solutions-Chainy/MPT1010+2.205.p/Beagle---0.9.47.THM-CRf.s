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
% DateTime   : Thu Dec  3 10:15:32 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   71 (  85 expanded)
%              Number of leaves         :   41 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 158 expanded)
%              Number of equality atoms :   73 (  87 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

tff(f_74,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(c_72,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_138,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_147,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_138])).

tff(c_150,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_147])).

tff(c_22,plain,(
    ! [B_35] : k4_xboole_0(k1_tarski(B_35),k1_tarski(B_35)) != k1_tarski(B_35) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_151,plain,(
    ! [B_35] : k1_tarski(B_35) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_22])).

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
    ! [D_173,C_174,B_175,A_176] :
      ( r2_hidden(k1_funct_1(D_173,C_174),B_175)
      | k1_xboole_0 = B_175
      | ~ r2_hidden(C_174,A_176)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(A_176,B_175)))
      | ~ v1_funct_2(D_173,A_176,B_175)
      | ~ v1_funct_1(D_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_415,plain,(
    ! [D_201,B_202] :
      ( r2_hidden(k1_funct_1(D_201,'#skF_5'),B_202)
      | k1_xboole_0 = B_202
      | ~ m1_subset_1(D_201,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_202)))
      | ~ v1_funct_2(D_201,'#skF_3',B_202)
      | ~ v1_funct_1(D_201) ) ),
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
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_enumset1(A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k4_enumset1(A_16,A_16,B_17,C_18,D_19,E_20) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_280,plain,(
    ! [C_160,A_156,B_159,H_157,D_158,F_155,E_161] :
      ( H_157 = F_155
      | H_157 = E_161
      | H_157 = D_158
      | H_157 = C_160
      | H_157 = B_159
      | H_157 = A_156
      | ~ r2_hidden(H_157,k4_enumset1(A_156,B_159,C_160,D_158,E_161,F_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_426,plain,(
    ! [B_203,A_205,D_207,H_206,E_204,C_208] :
      ( H_206 = E_204
      | H_206 = D_207
      | H_206 = C_208
      | H_206 = B_203
      | H_206 = A_205
      | H_206 = A_205
      | ~ r2_hidden(H_206,k3_enumset1(A_205,B_203,C_208,D_207,E_204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_280])).

tff(c_456,plain,(
    ! [B_211,H_215,C_214,D_213,A_212] :
      ( H_215 = D_213
      | H_215 = C_214
      | H_215 = B_211
      | H_215 = A_212
      | H_215 = A_212
      | H_215 = A_212
      | ~ r2_hidden(H_215,k2_enumset1(A_212,B_211,C_214,D_213)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_426])).

tff(c_480,plain,(
    ! [H_216,C_217,B_218,A_219] :
      ( H_216 = C_217
      | H_216 = B_218
      | H_216 = A_219
      | H_216 = A_219
      | H_216 = A_219
      | H_216 = A_219
      | ~ r2_hidden(H_216,k1_enumset1(A_219,B_218,C_217)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_456])).

tff(c_499,plain,(
    ! [H_220,B_221,A_222] :
      ( H_220 = B_221
      | H_220 = A_222
      | H_220 = A_222
      | H_220 = A_222
      | H_220 = A_222
      | H_220 = A_222
      | ~ r2_hidden(H_220,k2_tarski(A_222,B_221)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_480])).

tff(c_513,plain,(
    ! [H_223,A_224] :
      ( H_223 = A_224
      | H_223 = A_224
      | H_223 = A_224
      | H_223 = A_224
      | H_223 = A_224
      | H_223 = A_224
      | ~ r2_hidden(H_223,k1_tarski(A_224)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_499])).

tff(c_516,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_422,c_513])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_72,c_72,c_72,c_72,c_72,c_516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:04:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.43  
% 2.95/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.44  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.95/1.44  
% 2.95/1.44  %Foreground sorts:
% 2.95/1.44  
% 2.95/1.44  
% 2.95/1.44  %Background operators:
% 2.95/1.44  
% 2.95/1.44  
% 2.95/1.44  %Foreground operators:
% 2.95/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.95/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.95/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.95/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.95/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.95/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.95/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.95/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.95/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.95/1.44  
% 2.95/1.45  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.95/1.45  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.95/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.95/1.45  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.95/1.45  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.95/1.45  tff(f_88, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.95/1.45  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.95/1.45  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.95/1.45  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.95/1.45  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.95/1.45  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.95/1.45  tff(f_74, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 2.95/1.45  tff(c_72, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.95/1.45  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.45  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.95/1.45  tff(c_138, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.95/1.45  tff(c_147, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_138])).
% 2.95/1.45  tff(c_150, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_147])).
% 2.95/1.45  tff(c_22, plain, (![B_35]: (k4_xboole_0(k1_tarski(B_35), k1_tarski(B_35))!=k1_tarski(B_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.95/1.45  tff(c_151, plain, (![B_35]: (k1_tarski(B_35)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_22])).
% 2.95/1.45  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.95/1.45  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.95/1.45  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.95/1.45  tff(c_74, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.95/1.45  tff(c_328, plain, (![D_173, C_174, B_175, A_176]: (r2_hidden(k1_funct_1(D_173, C_174), B_175) | k1_xboole_0=B_175 | ~r2_hidden(C_174, A_176) | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(A_176, B_175))) | ~v1_funct_2(D_173, A_176, B_175) | ~v1_funct_1(D_173))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.95/1.45  tff(c_415, plain, (![D_201, B_202]: (r2_hidden(k1_funct_1(D_201, '#skF_5'), B_202) | k1_xboole_0=B_202 | ~m1_subset_1(D_201, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_202))) | ~v1_funct_2(D_201, '#skF_3', B_202) | ~v1_funct_1(D_201))), inference(resolution, [status(thm)], [c_74, c_328])).
% 2.95/1.45  tff(c_418, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_415])).
% 2.95/1.45  tff(c_421, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_418])).
% 2.95/1.45  tff(c_422, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_151, c_421])).
% 2.95/1.45  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.45  tff(c_10, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.45  tff(c_12, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.95/1.45  tff(c_14, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.95/1.45  tff(c_16, plain, (![C_18, B_17, A_16, D_19, E_20]: (k4_enumset1(A_16, A_16, B_17, C_18, D_19, E_20)=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.95/1.45  tff(c_280, plain, (![C_160, A_156, B_159, H_157, D_158, F_155, E_161]: (H_157=F_155 | H_157=E_161 | H_157=D_158 | H_157=C_160 | H_157=B_159 | H_157=A_156 | ~r2_hidden(H_157, k4_enumset1(A_156, B_159, C_160, D_158, E_161, F_155)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.95/1.45  tff(c_426, plain, (![B_203, A_205, D_207, H_206, E_204, C_208]: (H_206=E_204 | H_206=D_207 | H_206=C_208 | H_206=B_203 | H_206=A_205 | H_206=A_205 | ~r2_hidden(H_206, k3_enumset1(A_205, B_203, C_208, D_207, E_204)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_280])).
% 2.95/1.45  tff(c_456, plain, (![B_211, H_215, C_214, D_213, A_212]: (H_215=D_213 | H_215=C_214 | H_215=B_211 | H_215=A_212 | H_215=A_212 | H_215=A_212 | ~r2_hidden(H_215, k2_enumset1(A_212, B_211, C_214, D_213)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_426])).
% 2.95/1.45  tff(c_480, plain, (![H_216, C_217, B_218, A_219]: (H_216=C_217 | H_216=B_218 | H_216=A_219 | H_216=A_219 | H_216=A_219 | H_216=A_219 | ~r2_hidden(H_216, k1_enumset1(A_219, B_218, C_217)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_456])).
% 2.95/1.45  tff(c_499, plain, (![H_220, B_221, A_222]: (H_220=B_221 | H_220=A_222 | H_220=A_222 | H_220=A_222 | H_220=A_222 | H_220=A_222 | ~r2_hidden(H_220, k2_tarski(A_222, B_221)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_480])).
% 2.95/1.45  tff(c_513, plain, (![H_223, A_224]: (H_223=A_224 | H_223=A_224 | H_223=A_224 | H_223=A_224 | H_223=A_224 | H_223=A_224 | ~r2_hidden(H_223, k1_tarski(A_224)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_499])).
% 2.95/1.45  tff(c_516, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_422, c_513])).
% 2.95/1.45  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_72, c_72, c_72, c_72, c_72, c_516])).
% 2.95/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.45  
% 2.95/1.45  Inference rules
% 2.95/1.45  ----------------------
% 2.95/1.45  #Ref     : 0
% 2.95/1.45  #Sup     : 103
% 2.95/1.45  #Fact    : 0
% 2.95/1.45  #Define  : 0
% 2.95/1.45  #Split   : 0
% 2.95/1.45  #Chain   : 0
% 2.95/1.45  #Close   : 0
% 2.95/1.45  
% 2.95/1.45  Ordering : KBO
% 2.95/1.45  
% 2.95/1.45  Simplification rules
% 2.95/1.45  ----------------------
% 2.95/1.45  #Subsume      : 0
% 2.95/1.45  #Demod        : 10
% 2.95/1.45  #Tautology    : 55
% 2.95/1.45  #SimpNegUnit  : 4
% 2.95/1.45  #BackRed      : 1
% 2.95/1.45  
% 2.95/1.45  #Partial instantiations: 0
% 2.95/1.45  #Strategies tried      : 1
% 2.95/1.45  
% 2.95/1.45  Timing (in seconds)
% 2.95/1.45  ----------------------
% 2.95/1.45  Preprocessing        : 0.36
% 2.95/1.45  Parsing              : 0.18
% 2.95/1.45  CNF conversion       : 0.03
% 2.95/1.45  Main loop            : 0.32
% 2.95/1.45  Inferencing          : 0.11
% 2.95/1.45  Reduction            : 0.10
% 2.95/1.45  Demodulation         : 0.07
% 2.95/1.45  BG Simplification    : 0.02
% 2.95/1.45  Subsumption          : 0.07
% 2.95/1.45  Abstraction          : 0.02
% 2.95/1.45  MUC search           : 0.00
% 2.95/1.45  Cooper               : 0.00
% 2.95/1.45  Total                : 0.71
% 2.95/1.45  Index Insertion      : 0.00
% 2.95/1.46  Index Deletion       : 0.00
% 2.95/1.46  Index Matching       : 0.00
% 2.95/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
