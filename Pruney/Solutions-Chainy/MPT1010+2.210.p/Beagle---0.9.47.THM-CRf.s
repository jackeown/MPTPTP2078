%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:33 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 101 expanded)
%              Number of leaves         :   44 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 212 expanded)
%              Number of equality atoms :  111 ( 131 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_80,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

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

tff(f_78,axiom,(
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

tff(c_84,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_46] : k1_setfam_1(k1_tarski(A_46)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_127,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_118])).

tff(c_130,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_127])).

tff(c_150,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_159,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k4_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_150])).

tff(c_162,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_159])).

tff(c_20,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_163,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_20])).

tff(c_92,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_90,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_88,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_86,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_271,plain,(
    ! [D_157,C_158,B_159,A_160] :
      ( r2_hidden(k1_funct_1(D_157,C_158),B_159)
      | k1_xboole_0 = B_159
      | ~ r2_hidden(C_158,A_160)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_2(D_157,A_160,B_159)
      | ~ v1_funct_1(D_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_396,plain,(
    ! [D_205,B_206] :
      ( r2_hidden(k1_funct_1(D_205,'#skF_5'),B_206)
      | k1_xboole_0 = B_206
      | ~ m1_subset_1(D_205,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_206)))
      | ~ v1_funct_2(D_205,'#skF_3',B_206)
      | ~ v1_funct_1(D_205) ) ),
    inference(resolution,[status(thm)],[c_86,c_271])).

tff(c_399,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_396])).

tff(c_402,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_399])).

tff(c_403,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_402])).

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

tff(c_18,plain,(
    ! [A_25,G_31,F_30,E_29,C_27,D_28,B_26] : k6_enumset1(A_25,A_25,B_26,C_27,D_28,E_29,F_30,G_31) = k5_enumset1(A_25,B_26,C_27,D_28,E_29,F_30,G_31) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_334,plain,(
    ! [B_192,J_186,D_188,F_189,A_187,E_190,C_194,G_193,H_191] :
      ( J_186 = H_191
      | J_186 = G_193
      | J_186 = F_189
      | J_186 = E_190
      | J_186 = D_188
      | J_186 = C_194
      | J_186 = B_192
      | J_186 = A_187
      | ~ r2_hidden(J_186,k6_enumset1(A_187,B_192,C_194,D_188,E_190,F_189,G_193,H_191)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_586,plain,(
    ! [J_388,E_392,C_389,G_386,D_385,F_390,B_391,A_387] :
      ( J_388 = G_386
      | J_388 = F_390
      | J_388 = E_392
      | J_388 = D_385
      | J_388 = C_389
      | J_388 = B_391
      | J_388 = A_387
      | J_388 = A_387
      | ~ r2_hidden(J_388,k5_enumset1(A_387,B_391,C_389,D_385,E_392,F_390,G_386)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_334])).

tff(c_626,plain,(
    ! [E_403,F_407,C_402,D_408,J_404,B_405,A_406] :
      ( J_404 = F_407
      | J_404 = E_403
      | J_404 = D_408
      | J_404 = C_402
      | J_404 = B_405
      | J_404 = A_406
      | J_404 = A_406
      | J_404 = A_406
      | ~ r2_hidden(J_404,k4_enumset1(A_406,B_405,C_402,D_408,E_403,F_407)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_586])).

tff(c_660,plain,(
    ! [C_412,J_411,E_409,B_413,D_410,A_414] :
      ( J_411 = E_409
      | J_411 = D_410
      | J_411 = C_412
      | J_411 = B_413
      | J_411 = A_414
      | J_411 = A_414
      | J_411 = A_414
      | J_411 = A_414
      | ~ r2_hidden(J_411,k3_enumset1(A_414,B_413,C_412,D_410,E_409)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_626])).

tff(c_689,plain,(
    ! [C_419,D_418,B_416,A_417,J_415] :
      ( J_415 = D_418
      | J_415 = C_419
      | J_415 = B_416
      | J_415 = A_417
      | J_415 = A_417
      | J_415 = A_417
      | J_415 = A_417
      | J_415 = A_417
      | ~ r2_hidden(J_415,k2_enumset1(A_417,B_416,C_419,D_418)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_660])).

tff(c_714,plain,(
    ! [J_429,C_430,B_431,A_432] :
      ( J_429 = C_430
      | J_429 = B_431
      | J_429 = A_432
      | J_429 = A_432
      | J_429 = A_432
      | J_429 = A_432
      | J_429 = A_432
      | J_429 = A_432
      | ~ r2_hidden(J_429,k1_enumset1(A_432,B_431,C_430)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_689])).

tff(c_733,plain,(
    ! [J_433,B_434,A_435] :
      ( J_433 = B_434
      | J_433 = A_435
      | J_433 = A_435
      | J_433 = A_435
      | J_433 = A_435
      | J_433 = A_435
      | J_433 = A_435
      | J_433 = A_435
      | ~ r2_hidden(J_433,k2_tarski(A_435,B_434)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_714])).

tff(c_747,plain,(
    ! [J_436,A_437] :
      ( J_436 = A_437
      | J_436 = A_437
      | J_436 = A_437
      | J_436 = A_437
      | J_436 = A_437
      | J_436 = A_437
      | J_436 = A_437
      | J_436 = A_437
      | ~ r2_hidden(J_436,k1_tarski(A_437)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_733])).

tff(c_750,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_403,c_747])).

tff(c_757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_84,c_84,c_84,c_84,c_84,c_84,c_84,c_750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:01:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.53  
% 3.55/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.53  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.55/1.53  
% 3.55/1.53  %Foreground sorts:
% 3.55/1.53  
% 3.55/1.53  
% 3.55/1.53  %Background operators:
% 3.55/1.53  
% 3.55/1.53  
% 3.55/1.53  %Foreground operators:
% 3.55/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.55/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.55/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.55/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.55/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.55/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.55/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.55/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.55/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.55/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.55/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.55/1.53  
% 3.70/1.55  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.70/1.55  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.70/1.55  tff(f_80, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.70/1.55  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.70/1.55  tff(f_82, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.70/1.55  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.70/1.55  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.70/1.55  tff(f_94, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.70/1.55  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.70/1.55  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.70/1.55  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.70/1.55  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.70/1.55  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.70/1.55  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.70/1.55  tff(f_78, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.70/1.55  tff(c_84, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.70/1.55  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.70/1.55  tff(c_78, plain, (![A_46]: (k1_setfam_1(k1_tarski(A_46))=A_46)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.70/1.55  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.55  tff(c_118, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.70/1.55  tff(c_127, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_118])).
% 3.70/1.55  tff(c_130, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_127])).
% 3.70/1.55  tff(c_150, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.70/1.55  tff(c_159, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k4_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_130, c_150])).
% 3.70/1.55  tff(c_162, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_159])).
% 3.70/1.55  tff(c_20, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.70/1.55  tff(c_163, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_20])).
% 3.70/1.55  tff(c_92, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.70/1.55  tff(c_90, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.70/1.55  tff(c_88, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.70/1.55  tff(c_86, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.70/1.55  tff(c_271, plain, (![D_157, C_158, B_159, A_160]: (r2_hidden(k1_funct_1(D_157, C_158), B_159) | k1_xboole_0=B_159 | ~r2_hidden(C_158, A_160) | ~m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_2(D_157, A_160, B_159) | ~v1_funct_1(D_157))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.70/1.55  tff(c_396, plain, (![D_205, B_206]: (r2_hidden(k1_funct_1(D_205, '#skF_5'), B_206) | k1_xboole_0=B_206 | ~m1_subset_1(D_205, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_206))) | ~v1_funct_2(D_205, '#skF_3', B_206) | ~v1_funct_1(D_205))), inference(resolution, [status(thm)], [c_86, c_271])).
% 3.70/1.55  tff(c_399, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_88, c_396])).
% 3.70/1.55  tff(c_402, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_399])).
% 3.70/1.55  tff(c_403, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_163, c_402])).
% 3.70/1.55  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.70/1.55  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.70/1.55  tff(c_12, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.70/1.55  tff(c_14, plain, (![E_18, C_16, D_17, A_14, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, D_17, E_18)=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.70/1.55  tff(c_16, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, F_24)=k4_enumset1(A_19, B_20, C_21, D_22, E_23, F_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.70/1.55  tff(c_18, plain, (![A_25, G_31, F_30, E_29, C_27, D_28, B_26]: (k6_enumset1(A_25, A_25, B_26, C_27, D_28, E_29, F_30, G_31)=k5_enumset1(A_25, B_26, C_27, D_28, E_29, F_30, G_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.70/1.55  tff(c_334, plain, (![B_192, J_186, D_188, F_189, A_187, E_190, C_194, G_193, H_191]: (J_186=H_191 | J_186=G_193 | J_186=F_189 | J_186=E_190 | J_186=D_188 | J_186=C_194 | J_186=B_192 | J_186=A_187 | ~r2_hidden(J_186, k6_enumset1(A_187, B_192, C_194, D_188, E_190, F_189, G_193, H_191)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.70/1.55  tff(c_586, plain, (![J_388, E_392, C_389, G_386, D_385, F_390, B_391, A_387]: (J_388=G_386 | J_388=F_390 | J_388=E_392 | J_388=D_385 | J_388=C_389 | J_388=B_391 | J_388=A_387 | J_388=A_387 | ~r2_hidden(J_388, k5_enumset1(A_387, B_391, C_389, D_385, E_392, F_390, G_386)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_334])).
% 3.70/1.55  tff(c_626, plain, (![E_403, F_407, C_402, D_408, J_404, B_405, A_406]: (J_404=F_407 | J_404=E_403 | J_404=D_408 | J_404=C_402 | J_404=B_405 | J_404=A_406 | J_404=A_406 | J_404=A_406 | ~r2_hidden(J_404, k4_enumset1(A_406, B_405, C_402, D_408, E_403, F_407)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_586])).
% 3.70/1.55  tff(c_660, plain, (![C_412, J_411, E_409, B_413, D_410, A_414]: (J_411=E_409 | J_411=D_410 | J_411=C_412 | J_411=B_413 | J_411=A_414 | J_411=A_414 | J_411=A_414 | J_411=A_414 | ~r2_hidden(J_411, k3_enumset1(A_414, B_413, C_412, D_410, E_409)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_626])).
% 3.70/1.55  tff(c_689, plain, (![C_419, D_418, B_416, A_417, J_415]: (J_415=D_418 | J_415=C_419 | J_415=B_416 | J_415=A_417 | J_415=A_417 | J_415=A_417 | J_415=A_417 | J_415=A_417 | ~r2_hidden(J_415, k2_enumset1(A_417, B_416, C_419, D_418)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_660])).
% 3.70/1.55  tff(c_714, plain, (![J_429, C_430, B_431, A_432]: (J_429=C_430 | J_429=B_431 | J_429=A_432 | J_429=A_432 | J_429=A_432 | J_429=A_432 | J_429=A_432 | J_429=A_432 | ~r2_hidden(J_429, k1_enumset1(A_432, B_431, C_430)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_689])).
% 3.70/1.55  tff(c_733, plain, (![J_433, B_434, A_435]: (J_433=B_434 | J_433=A_435 | J_433=A_435 | J_433=A_435 | J_433=A_435 | J_433=A_435 | J_433=A_435 | J_433=A_435 | ~r2_hidden(J_433, k2_tarski(A_435, B_434)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_714])).
% 3.70/1.55  tff(c_747, plain, (![J_436, A_437]: (J_436=A_437 | J_436=A_437 | J_436=A_437 | J_436=A_437 | J_436=A_437 | J_436=A_437 | J_436=A_437 | J_436=A_437 | ~r2_hidden(J_436, k1_tarski(A_437)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_733])).
% 3.70/1.55  tff(c_750, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_403, c_747])).
% 3.70/1.55  tff(c_757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_84, c_84, c_84, c_84, c_84, c_84, c_84, c_750])).
% 3.70/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.55  
% 3.70/1.55  Inference rules
% 3.70/1.55  ----------------------
% 3.70/1.55  #Ref     : 0
% 3.70/1.55  #Sup     : 155
% 3.70/1.55  #Fact    : 0
% 3.70/1.55  #Define  : 0
% 3.70/1.55  #Split   : 0
% 3.70/1.55  #Chain   : 0
% 3.70/1.55  #Close   : 0
% 3.70/1.55  
% 3.70/1.55  Ordering : KBO
% 3.70/1.55  
% 3.70/1.55  Simplification rules
% 3.70/1.55  ----------------------
% 3.70/1.55  #Subsume      : 5
% 3.70/1.55  #Demod        : 17
% 3.70/1.55  #Tautology    : 72
% 3.70/1.55  #SimpNegUnit  : 4
% 3.70/1.55  #BackRed      : 1
% 3.70/1.55  
% 3.70/1.55  #Partial instantiations: 0
% 3.70/1.55  #Strategies tried      : 1
% 3.70/1.55  
% 3.70/1.55  Timing (in seconds)
% 3.70/1.55  ----------------------
% 3.70/1.55  Preprocessing        : 0.36
% 3.70/1.55  Parsing              : 0.17
% 3.70/1.55  CNF conversion       : 0.03
% 3.70/1.55  Main loop            : 0.41
% 3.70/1.55  Inferencing          : 0.15
% 3.70/1.55  Reduction            : 0.12
% 3.70/1.55  Demodulation         : 0.09
% 3.70/1.55  BG Simplification    : 0.03
% 3.70/1.55  Subsumption          : 0.10
% 3.70/1.55  Abstraction          : 0.03
% 3.70/1.55  MUC search           : 0.00
% 3.70/1.55  Cooper               : 0.00
% 3.70/1.55  Total                : 0.80
% 3.70/1.55  Index Insertion      : 0.00
% 3.70/1.55  Index Deletion       : 0.00
% 3.70/1.55  Index Matching       : 0.00
% 3.70/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
