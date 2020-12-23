%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:33 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   78 (  96 expanded)
%              Number of leaves         :   43 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  129 ( 187 expanded)
%              Number of equality atoms :   93 ( 111 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_102,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_79,axiom,(
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

tff(f_91,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( H = k5_enumset1(A,B,C,D,E,F,G)
    <=> ! [I] :
          ( r2_hidden(I,H)
        <=> ~ ( I != A
              & I != B
              & I != C
              & I != D
              & I != E
              & I != F
              & I != G ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

tff(c_78,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_45] : k1_setfam_1(k1_tarski(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_55,B_56] : k1_setfam_1(k2_tarski(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_121,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_112])).

tff(c_124,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_121])).

tff(c_144,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_153,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k4_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_144])).

tff(c_156,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_153])).

tff(c_20,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_157,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_20])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_84,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_80,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_286,plain,(
    ! [D_168,C_169,B_170,A_171] :
      ( r2_hidden(k1_funct_1(D_168,C_169),B_170)
      | k1_xboole_0 = B_170
      | ~ r2_hidden(C_169,A_171)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(A_171,B_170)))
      | ~ v1_funct_2(D_168,A_171,B_170)
      | ~ v1_funct_1(D_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_349,plain,(
    ! [D_183,B_184] :
      ( r2_hidden(k1_funct_1(D_183,'#skF_5'),B_184)
      | k1_xboole_0 = B_184
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_184)))
      | ~ v1_funct_2(D_183,'#skF_3',B_184)
      | ~ v1_funct_1(D_183) ) ),
    inference(resolution,[status(thm)],[c_80,c_286])).

tff(c_352,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_349])).

tff(c_355,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_352])).

tff(c_356,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_355])).

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

tff(c_16,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] : k5_enumset1(A_19,A_19,B_20,C_21,D_22,E_23,F_24) = k4_enumset1(A_19,B_20,C_21,D_22,E_23,F_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_388,plain,(
    ! [C_209,E_206,D_204,A_203,F_205,B_207,G_208,I_210] :
      ( I_210 = G_208
      | I_210 = F_205
      | I_210 = E_206
      | I_210 = D_204
      | I_210 = C_209
      | I_210 = B_207
      | I_210 = A_203
      | ~ r2_hidden(I_210,k5_enumset1(A_203,B_207,C_209,D_204,E_206,F_205,G_208)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_489,plain,(
    ! [A_263,I_261,F_264,B_262,D_265,C_259,E_260] :
      ( I_261 = F_264
      | I_261 = E_260
      | I_261 = D_265
      | I_261 = C_259
      | I_261 = B_262
      | I_261 = A_263
      | I_261 = A_263
      | ~ r2_hidden(I_261,k4_enumset1(A_263,B_262,C_259,D_265,E_260,F_264)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_388])).

tff(c_523,plain,(
    ! [D_268,E_267,B_270,A_271,C_269,I_266] :
      ( I_266 = E_267
      | I_266 = D_268
      | I_266 = C_269
      | I_266 = B_270
      | I_266 = A_271
      | I_266 = A_271
      | I_266 = A_271
      | ~ r2_hidden(I_266,k3_enumset1(A_271,B_270,C_269,D_268,E_267)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_489])).

tff(c_553,plain,(
    ! [C_284,B_280,D_282,I_283,A_281] :
      ( I_283 = D_282
      | I_283 = C_284
      | I_283 = B_280
      | I_283 = A_281
      | I_283 = A_281
      | I_283 = A_281
      | I_283 = A_281
      | ~ r2_hidden(I_283,k2_enumset1(A_281,B_280,C_284,D_282)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_523])).

tff(c_577,plain,(
    ! [I_285,C_286,B_287,A_288] :
      ( I_285 = C_286
      | I_285 = B_287
      | I_285 = A_288
      | I_285 = A_288
      | I_285 = A_288
      | I_285 = A_288
      | I_285 = A_288
      | ~ r2_hidden(I_285,k1_enumset1(A_288,B_287,C_286)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_553])).

tff(c_596,plain,(
    ! [I_289,B_290,A_291] :
      ( I_289 = B_290
      | I_289 = A_291
      | I_289 = A_291
      | I_289 = A_291
      | I_289 = A_291
      | I_289 = A_291
      | I_289 = A_291
      | ~ r2_hidden(I_289,k2_tarski(A_291,B_290)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_577])).

tff(c_610,plain,(
    ! [I_292,A_293] :
      ( I_292 = A_293
      | I_292 = A_293
      | I_292 = A_293
      | I_292 = A_293
      | I_292 = A_293
      | I_292 = A_293
      | I_292 = A_293
      | ~ r2_hidden(I_292,k1_tarski(A_293)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_596])).

tff(c_613,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_356,c_610])).

tff(c_620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_78,c_78,c_78,c_78,c_78,c_78,c_613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:03:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.46  
% 3.14/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.46  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.14/1.46  
% 3.14/1.46  %Foreground sorts:
% 3.14/1.46  
% 3.14/1.46  
% 3.14/1.46  %Background operators:
% 3.14/1.46  
% 3.14/1.46  
% 3.14/1.46  %Foreground operators:
% 3.14/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.14/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.14/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.14/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.14/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.14/1.46  
% 3.14/1.48  tff(f_102, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.14/1.48  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.14/1.48  tff(f_77, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.14/1.48  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.14/1.48  tff(f_79, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.14/1.48  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.14/1.48  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.14/1.48  tff(f_91, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.14/1.48  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.14/1.48  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.14/1.48  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.14/1.48  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.14/1.48  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.14/1.48  tff(f_75, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 3.14/1.48  tff(c_78, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.14/1.48  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.48  tff(c_72, plain, (![A_45]: (k1_setfam_1(k1_tarski(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.14/1.48  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.48  tff(c_112, plain, (![A_55, B_56]: (k1_setfam_1(k2_tarski(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.14/1.48  tff(c_121, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_112])).
% 3.14/1.48  tff(c_124, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_121])).
% 3.14/1.48  tff(c_144, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.48  tff(c_153, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k4_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_124, c_144])).
% 3.14/1.48  tff(c_156, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_153])).
% 3.14/1.48  tff(c_20, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.48  tff(c_157, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_20])).
% 3.14/1.48  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.14/1.48  tff(c_84, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.14/1.48  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.14/1.48  tff(c_80, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.14/1.48  tff(c_286, plain, (![D_168, C_169, B_170, A_171]: (r2_hidden(k1_funct_1(D_168, C_169), B_170) | k1_xboole_0=B_170 | ~r2_hidden(C_169, A_171) | ~m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(A_171, B_170))) | ~v1_funct_2(D_168, A_171, B_170) | ~v1_funct_1(D_168))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.14/1.48  tff(c_349, plain, (![D_183, B_184]: (r2_hidden(k1_funct_1(D_183, '#skF_5'), B_184) | k1_xboole_0=B_184 | ~m1_subset_1(D_183, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_184))) | ~v1_funct_2(D_183, '#skF_3', B_184) | ~v1_funct_1(D_183))), inference(resolution, [status(thm)], [c_80, c_286])).
% 3.14/1.48  tff(c_352, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_349])).
% 3.14/1.48  tff(c_355, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_352])).
% 3.14/1.48  tff(c_356, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_157, c_355])).
% 3.14/1.48  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.14/1.48  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.48  tff(c_12, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.14/1.48  tff(c_14, plain, (![E_18, C_16, D_17, A_14, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, D_17, E_18)=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.14/1.48  tff(c_16, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, F_24)=k4_enumset1(A_19, B_20, C_21, D_22, E_23, F_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.14/1.48  tff(c_388, plain, (![C_209, E_206, D_204, A_203, F_205, B_207, G_208, I_210]: (I_210=G_208 | I_210=F_205 | I_210=E_206 | I_210=D_204 | I_210=C_209 | I_210=B_207 | I_210=A_203 | ~r2_hidden(I_210, k5_enumset1(A_203, B_207, C_209, D_204, E_206, F_205, G_208)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.14/1.48  tff(c_489, plain, (![A_263, I_261, F_264, B_262, D_265, C_259, E_260]: (I_261=F_264 | I_261=E_260 | I_261=D_265 | I_261=C_259 | I_261=B_262 | I_261=A_263 | I_261=A_263 | ~r2_hidden(I_261, k4_enumset1(A_263, B_262, C_259, D_265, E_260, F_264)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_388])).
% 3.14/1.48  tff(c_523, plain, (![D_268, E_267, B_270, A_271, C_269, I_266]: (I_266=E_267 | I_266=D_268 | I_266=C_269 | I_266=B_270 | I_266=A_271 | I_266=A_271 | I_266=A_271 | ~r2_hidden(I_266, k3_enumset1(A_271, B_270, C_269, D_268, E_267)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_489])).
% 3.14/1.48  tff(c_553, plain, (![C_284, B_280, D_282, I_283, A_281]: (I_283=D_282 | I_283=C_284 | I_283=B_280 | I_283=A_281 | I_283=A_281 | I_283=A_281 | I_283=A_281 | ~r2_hidden(I_283, k2_enumset1(A_281, B_280, C_284, D_282)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_523])).
% 3.14/1.48  tff(c_577, plain, (![I_285, C_286, B_287, A_288]: (I_285=C_286 | I_285=B_287 | I_285=A_288 | I_285=A_288 | I_285=A_288 | I_285=A_288 | I_285=A_288 | ~r2_hidden(I_285, k1_enumset1(A_288, B_287, C_286)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_553])).
% 3.14/1.48  tff(c_596, plain, (![I_289, B_290, A_291]: (I_289=B_290 | I_289=A_291 | I_289=A_291 | I_289=A_291 | I_289=A_291 | I_289=A_291 | I_289=A_291 | ~r2_hidden(I_289, k2_tarski(A_291, B_290)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_577])).
% 3.14/1.48  tff(c_610, plain, (![I_292, A_293]: (I_292=A_293 | I_292=A_293 | I_292=A_293 | I_292=A_293 | I_292=A_293 | I_292=A_293 | I_292=A_293 | ~r2_hidden(I_292, k1_tarski(A_293)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_596])).
% 3.14/1.48  tff(c_613, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_356, c_610])).
% 3.14/1.48  tff(c_620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_78, c_78, c_78, c_78, c_78, c_78, c_613])).
% 3.14/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.48  
% 3.14/1.48  Inference rules
% 3.14/1.48  ----------------------
% 3.14/1.48  #Ref     : 0
% 3.14/1.48  #Sup     : 125
% 3.14/1.48  #Fact    : 0
% 3.14/1.48  #Define  : 0
% 3.14/1.48  #Split   : 0
% 3.14/1.48  #Chain   : 0
% 3.14/1.48  #Close   : 0
% 3.14/1.48  
% 3.14/1.48  Ordering : KBO
% 3.14/1.48  
% 3.14/1.48  Simplification rules
% 3.14/1.48  ----------------------
% 3.14/1.48  #Subsume      : 0
% 3.14/1.48  #Demod        : 11
% 3.14/1.48  #Tautology    : 63
% 3.14/1.48  #SimpNegUnit  : 4
% 3.14/1.48  #BackRed      : 1
% 3.14/1.48  
% 3.14/1.48  #Partial instantiations: 0
% 3.14/1.48  #Strategies tried      : 1
% 3.14/1.48  
% 3.14/1.48  Timing (in seconds)
% 3.14/1.48  ----------------------
% 3.14/1.48  Preprocessing        : 0.35
% 3.14/1.48  Parsing              : 0.17
% 3.14/1.48  CNF conversion       : 0.03
% 3.14/1.48  Main loop            : 0.35
% 3.14/1.48  Inferencing          : 0.12
% 3.14/1.48  Reduction            : 0.10
% 3.14/1.48  Demodulation         : 0.08
% 3.14/1.48  BG Simplification    : 0.03
% 3.14/1.48  Subsumption          : 0.09
% 3.14/1.48  Abstraction          : 0.03
% 3.14/1.48  MUC search           : 0.00
% 3.14/1.48  Cooper               : 0.00
% 3.14/1.48  Total                : 0.74
% 3.14/1.48  Index Insertion      : 0.00
% 3.14/1.48  Index Deletion       : 0.00
% 3.14/1.48  Index Matching       : 0.00
% 3.14/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
