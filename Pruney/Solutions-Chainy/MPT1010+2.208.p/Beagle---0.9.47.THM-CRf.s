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
% DateTime   : Thu Dec  3 10:15:33 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 139 expanded)
%              Number of leaves         :   43 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 332 expanded)
%              Number of equality atoms :   94 ( 141 expanded)
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

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

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

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

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

tff(c_290,plain,(
    ! [D_161,C_162,B_163,A_164] :
      ( r2_hidden(k1_funct_1(D_161,C_162),B_163)
      | k1_xboole_0 = B_163
      | ~ r2_hidden(C_162,A_164)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_164,B_163)))
      | ~ v1_funct_2(D_161,A_164,B_163)
      | ~ v1_funct_1(D_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_355,plain,(
    ! [D_180,B_181] :
      ( r2_hidden(k1_funct_1(D_180,'#skF_5'),B_181)
      | k1_xboole_0 = B_181
      | ~ m1_subset_1(D_180,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_181)))
      | ~ v1_funct_2(D_180,'#skF_3',B_181)
      | ~ v1_funct_1(D_180) ) ),
    inference(resolution,[status(thm)],[c_80,c_290])).

tff(c_358,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_355])).

tff(c_361,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_358])).

tff(c_453,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_72,plain,(
    ! [A_45] : k1_setfam_1(k1_tarski(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_55,B_56] : k1_setfam_1(k2_tarski(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_123,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_114])).

tff(c_126,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_123])).

tff(c_146,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_158,plain,(
    ! [A_63] : k5_xboole_0(A_63,A_63) = k4_xboole_0(A_63,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_146])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_165,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_4])).

tff(c_20,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_468,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_4')) != k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_20])).

tff(c_480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_165,c_453,c_468])).

tff(c_481,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_361])).

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

tff(c_391,plain,(
    ! [I_207,B_204,A_200,C_206,F_202,D_201,E_203,G_205] :
      ( I_207 = G_205
      | I_207 = F_202
      | I_207 = E_203
      | I_207 = D_201
      | I_207 = C_206
      | I_207 = B_204
      | I_207 = A_200
      | ~ r2_hidden(I_207,k5_enumset1(A_200,B_204,C_206,D_201,E_203,F_202,G_205)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_526,plain,(
    ! [D_264,A_261,E_259,C_258,F_262,B_260,I_263] :
      ( I_263 = F_262
      | I_263 = E_259
      | I_263 = D_264
      | I_263 = C_258
      | I_263 = B_260
      | I_263 = A_261
      | I_263 = A_261
      | ~ r2_hidden(I_263,k4_enumset1(A_261,B_260,C_258,D_264,E_259,F_262)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_391])).

tff(c_560,plain,(
    ! [A_269,I_270,C_267,D_266,E_265,B_268] :
      ( I_270 = E_265
      | I_270 = D_266
      | I_270 = C_267
      | I_270 = B_268
      | I_270 = A_269
      | I_270 = A_269
      | I_270 = A_269
      | ~ r2_hidden(I_270,k3_enumset1(A_269,B_268,C_267,D_266,E_265)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_526])).

tff(c_589,plain,(
    ! [I_274,D_273,C_275,A_272,B_271] :
      ( I_274 = D_273
      | I_274 = C_275
      | I_274 = B_271
      | I_274 = A_272
      | I_274 = A_272
      | I_274 = A_272
      | I_274 = A_272
      | ~ r2_hidden(I_274,k2_enumset1(A_272,B_271,C_275,D_273)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_560])).

tff(c_613,plain,(
    ! [I_276,C_277,B_278,A_279] :
      ( I_276 = C_277
      | I_276 = B_278
      | I_276 = A_279
      | I_276 = A_279
      | I_276 = A_279
      | I_276 = A_279
      | I_276 = A_279
      | ~ r2_hidden(I_276,k1_enumset1(A_279,B_278,C_277)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_589])).

tff(c_633,plain,(
    ! [I_288,B_289,A_290] :
      ( I_288 = B_289
      | I_288 = A_290
      | I_288 = A_290
      | I_288 = A_290
      | I_288 = A_290
      | I_288 = A_290
      | I_288 = A_290
      | ~ r2_hidden(I_288,k2_tarski(A_290,B_289)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_613])).

tff(c_647,plain,(
    ! [I_291,A_292] :
      ( I_291 = A_292
      | I_291 = A_292
      | I_291 = A_292
      | I_291 = A_292
      | I_291 = A_292
      | I_291 = A_292
      | I_291 = A_292
      | ~ r2_hidden(I_291,k1_tarski(A_292)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_633])).

tff(c_650,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_481,c_647])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_78,c_78,c_78,c_78,c_78,c_78,c_650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:48:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.53  
% 3.33/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.53  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.33/1.53  
% 3.33/1.53  %Foreground sorts:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Background operators:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Foreground operators:
% 3.33/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.33/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.33/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.33/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.33/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.33/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.33/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.33/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.33/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.33/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.33/1.53  
% 3.45/1.54  tff(f_102, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.45/1.54  tff(f_91, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.45/1.54  tff(f_77, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.45/1.54  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.45/1.54  tff(f_79, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.45/1.54  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.45/1.54  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.45/1.54  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.45/1.54  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.45/1.54  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.45/1.54  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.45/1.54  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.45/1.54  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.45/1.54  tff(f_75, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 3.45/1.54  tff(c_78, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.45/1.54  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.45/1.54  tff(c_84, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.45/1.54  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.45/1.54  tff(c_80, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.45/1.54  tff(c_290, plain, (![D_161, C_162, B_163, A_164]: (r2_hidden(k1_funct_1(D_161, C_162), B_163) | k1_xboole_0=B_163 | ~r2_hidden(C_162, A_164) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_164, B_163))) | ~v1_funct_2(D_161, A_164, B_163) | ~v1_funct_1(D_161))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.45/1.54  tff(c_355, plain, (![D_180, B_181]: (r2_hidden(k1_funct_1(D_180, '#skF_5'), B_181) | k1_xboole_0=B_181 | ~m1_subset_1(D_180, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_181))) | ~v1_funct_2(D_180, '#skF_3', B_181) | ~v1_funct_1(D_180))), inference(resolution, [status(thm)], [c_80, c_290])).
% 3.45/1.54  tff(c_358, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_355])).
% 3.45/1.54  tff(c_361, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_358])).
% 3.45/1.54  tff(c_453, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_361])).
% 3.45/1.54  tff(c_72, plain, (![A_45]: (k1_setfam_1(k1_tarski(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.45/1.54  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.54  tff(c_114, plain, (![A_55, B_56]: (k1_setfam_1(k2_tarski(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.45/1.54  tff(c_123, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_114])).
% 3.45/1.54  tff(c_126, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_123])).
% 3.45/1.54  tff(c_146, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.45/1.54  tff(c_158, plain, (![A_63]: (k5_xboole_0(A_63, A_63)=k4_xboole_0(A_63, A_63))), inference(superposition, [status(thm), theory('equality')], [c_126, c_146])).
% 3.45/1.54  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.45/1.54  tff(c_165, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_158, c_4])).
% 3.45/1.54  tff(c_20, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.45/1.54  tff(c_468, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_4'))!=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_453, c_20])).
% 3.45/1.54  tff(c_480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_453, c_165, c_453, c_468])).
% 3.45/1.54  tff(c_481, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_361])).
% 3.45/1.54  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.45/1.54  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.45/1.54  tff(c_12, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.45/1.54  tff(c_14, plain, (![E_18, C_16, D_17, A_14, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, D_17, E_18)=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.45/1.54  tff(c_16, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, F_24)=k4_enumset1(A_19, B_20, C_21, D_22, E_23, F_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.45/1.54  tff(c_391, plain, (![I_207, B_204, A_200, C_206, F_202, D_201, E_203, G_205]: (I_207=G_205 | I_207=F_202 | I_207=E_203 | I_207=D_201 | I_207=C_206 | I_207=B_204 | I_207=A_200 | ~r2_hidden(I_207, k5_enumset1(A_200, B_204, C_206, D_201, E_203, F_202, G_205)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.45/1.54  tff(c_526, plain, (![D_264, A_261, E_259, C_258, F_262, B_260, I_263]: (I_263=F_262 | I_263=E_259 | I_263=D_264 | I_263=C_258 | I_263=B_260 | I_263=A_261 | I_263=A_261 | ~r2_hidden(I_263, k4_enumset1(A_261, B_260, C_258, D_264, E_259, F_262)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_391])).
% 3.45/1.54  tff(c_560, plain, (![A_269, I_270, C_267, D_266, E_265, B_268]: (I_270=E_265 | I_270=D_266 | I_270=C_267 | I_270=B_268 | I_270=A_269 | I_270=A_269 | I_270=A_269 | ~r2_hidden(I_270, k3_enumset1(A_269, B_268, C_267, D_266, E_265)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_526])).
% 3.45/1.54  tff(c_589, plain, (![I_274, D_273, C_275, A_272, B_271]: (I_274=D_273 | I_274=C_275 | I_274=B_271 | I_274=A_272 | I_274=A_272 | I_274=A_272 | I_274=A_272 | ~r2_hidden(I_274, k2_enumset1(A_272, B_271, C_275, D_273)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_560])).
% 3.45/1.54  tff(c_613, plain, (![I_276, C_277, B_278, A_279]: (I_276=C_277 | I_276=B_278 | I_276=A_279 | I_276=A_279 | I_276=A_279 | I_276=A_279 | I_276=A_279 | ~r2_hidden(I_276, k1_enumset1(A_279, B_278, C_277)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_589])).
% 3.45/1.54  tff(c_633, plain, (![I_288, B_289, A_290]: (I_288=B_289 | I_288=A_290 | I_288=A_290 | I_288=A_290 | I_288=A_290 | I_288=A_290 | I_288=A_290 | ~r2_hidden(I_288, k2_tarski(A_290, B_289)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_613])).
% 3.45/1.54  tff(c_647, plain, (![I_291, A_292]: (I_291=A_292 | I_291=A_292 | I_291=A_292 | I_291=A_292 | I_291=A_292 | I_291=A_292 | I_291=A_292 | ~r2_hidden(I_291, k1_tarski(A_292)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_633])).
% 3.45/1.54  tff(c_650, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_481, c_647])).
% 3.45/1.54  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_78, c_78, c_78, c_78, c_78, c_78, c_650])).
% 3.45/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.54  
% 3.45/1.54  Inference rules
% 3.45/1.54  ----------------------
% 3.45/1.54  #Ref     : 0
% 3.45/1.54  #Sup     : 136
% 3.45/1.54  #Fact    : 0
% 3.45/1.54  #Define  : 0
% 3.45/1.54  #Split   : 1
% 3.45/1.54  #Chain   : 0
% 3.45/1.54  #Close   : 0
% 3.45/1.54  
% 3.45/1.54  Ordering : KBO
% 3.45/1.54  
% 3.45/1.54  Simplification rules
% 3.45/1.54  ----------------------
% 3.45/1.54  #Subsume      : 0
% 3.45/1.54  #Demod        : 16
% 3.45/1.54  #Tautology    : 66
% 3.45/1.54  #SimpNegUnit  : 1
% 3.45/1.54  #BackRed      : 2
% 3.45/1.54  
% 3.45/1.54  #Partial instantiations: 0
% 3.45/1.54  #Strategies tried      : 1
% 3.45/1.54  
% 3.45/1.54  Timing (in seconds)
% 3.45/1.54  ----------------------
% 3.45/1.55  Preprocessing        : 0.38
% 3.45/1.55  Parsing              : 0.18
% 3.45/1.55  CNF conversion       : 0.03
% 3.45/1.55  Main loop            : 0.37
% 3.45/1.55  Inferencing          : 0.12
% 3.45/1.55  Reduction            : 0.11
% 3.45/1.55  Demodulation         : 0.08
% 3.45/1.55  BG Simplification    : 0.03
% 3.45/1.55  Subsumption          : 0.09
% 3.45/1.55  Abstraction          : 0.03
% 3.45/1.55  MUC search           : 0.00
% 3.45/1.55  Cooper               : 0.00
% 3.45/1.55  Total                : 0.77
% 3.45/1.55  Index Insertion      : 0.00
% 3.45/1.55  Index Deletion       : 0.00
% 3.45/1.55  Index Matching       : 0.00
% 3.45/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
