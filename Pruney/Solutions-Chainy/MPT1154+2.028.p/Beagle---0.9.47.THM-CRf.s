%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:36 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 175 expanded)
%              Number of leaves         :   42 (  84 expanded)
%              Depth                    :   10
%              Number of atoms          :  176 ( 529 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_69,axiom,(
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

tff(c_94,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_92,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_90,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_88,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_86,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_76,plain,(
    ! [A_48,B_50] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_48),B_50),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_50,u1_struct_0(A_48))
      | ~ l1_orders_2(A_48)
      | ~ v3_orders_2(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_82,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_251,plain,(
    ! [B_208,A_209,C_210] :
      ( ~ r2_hidden(B_208,k1_orders_2(A_209,C_210))
      | ~ r2_hidden(B_208,C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ m1_subset_1(B_208,u1_struct_0(A_209))
      | ~ l1_orders_2(A_209)
      | ~ v5_orders_2(A_209)
      | ~ v4_orders_2(A_209)
      | ~ v3_orders_2(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_253,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_251])).

tff(c_256,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_253])).

tff(c_257,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_256])).

tff(c_336,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_339,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_336])).

tff(c_342,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_86,c_84,c_339])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_342])).

tff(c_346,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_123,plain,(
    ! [A_68,B_69] :
      ( k6_domain_1(A_68,B_69) = k1_tarski(B_69)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_127,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_84,c_123])).

tff(c_128,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_231,plain,(
    ! [A_188,B_189] :
      ( m1_subset_1(k1_orders_2(A_188,B_189),k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_orders_2(A_188)
      | ~ v5_orders_2(A_188)
      | ~ v4_orders_2(A_188)
      | ~ v3_orders_2(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_70,plain,(
    ! [C_43,B_42,A_41] :
      ( ~ v1_xboole_0(C_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_407,plain,(
    ! [A_345,A_346,B_347] :
      ( ~ v1_xboole_0(u1_struct_0(A_345))
      | ~ r2_hidden(A_346,k1_orders_2(A_345,B_347))
      | ~ m1_subset_1(B_347,k1_zfmisc_1(u1_struct_0(A_345)))
      | ~ l1_orders_2(A_345)
      | ~ v5_orders_2(A_345)
      | ~ v4_orders_2(A_345)
      | ~ v3_orders_2(A_345)
      | v2_struct_0(A_345) ) ),
    inference(resolution,[status(thm)],[c_231,c_70])).

tff(c_409,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_407])).

tff(c_412,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_346,c_128,c_409])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_412])).

tff(c_415,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_497,plain,(
    ! [A_436,B_437] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_436),B_437),k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ m1_subset_1(B_437,u1_struct_0(A_436))
      | ~ l1_orders_2(A_436)
      | ~ v3_orders_2(A_436)
      | v2_struct_0(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_505,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_497])).

tff(c_509,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_86,c_84,c_505])).

tff(c_510,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_509])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_464,plain,(
    ! [B_435,G_433,E_431,C_430,D_434,A_429,F_432] : k6_enumset1(A_429,A_429,B_435,C_430,D_434,E_431,F_432,G_433) = k5_enumset1(A_429,B_435,C_430,D_434,E_431,F_432,G_433) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [G_35,H_36,E_33,J_40,A_29,D_32,C_31,B_30] : r2_hidden(J_40,k6_enumset1(A_29,B_30,C_31,D_32,E_33,J_40,G_35,H_36)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_518,plain,(
    ! [F_442,E_439,B_440,A_441,G_438,D_443,C_444] : r2_hidden(E_439,k5_enumset1(A_441,B_440,C_444,D_443,E_439,F_442,G_438)) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_22])).

tff(c_522,plain,(
    ! [F_445,C_450,E_447,B_446,A_448,D_449] : r2_hidden(D_449,k4_enumset1(A_448,B_446,C_450,D_449,E_447,F_445)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_518])).

tff(c_526,plain,(
    ! [B_453,D_454,A_452,E_455,C_451] : r2_hidden(C_451,k3_enumset1(A_452,B_453,C_451,D_454,E_455)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_522])).

tff(c_530,plain,(
    ! [B_456,A_457,C_458,D_459] : r2_hidden(B_456,k2_enumset1(A_457,B_456,C_458,D_459)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_526])).

tff(c_542,plain,(
    ! [A_462,B_463,C_464] : r2_hidden(A_462,k1_enumset1(A_462,B_463,C_464)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_530])).

tff(c_546,plain,(
    ! [A_465,B_466] : r2_hidden(A_465,k2_tarski(A_465,B_466)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_542])).

tff(c_549,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_546])).

tff(c_417,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_82])).

tff(c_622,plain,(
    ! [B_512,A_513,C_514] :
      ( ~ r2_hidden(B_512,k1_orders_2(A_513,C_514))
      | ~ r2_hidden(B_512,C_514)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(u1_struct_0(A_513)))
      | ~ m1_subset_1(B_512,u1_struct_0(A_513))
      | ~ l1_orders_2(A_513)
      | ~ v5_orders_2(A_513)
      | ~ v4_orders_2(A_513)
      | ~ v3_orders_2(A_513)
      | v2_struct_0(A_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_624,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_417,c_622])).

tff(c_627,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_510,c_549,c_624])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.58  
% 3.58/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.59  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.58/1.59  
% 3.58/1.59  %Foreground sorts:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Background operators:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Foreground operators:
% 3.58/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.58/1.59  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.58/1.59  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.58/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.58/1.59  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.58/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.58/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.58/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.58/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.58/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.59  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.58/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.58/1.59  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.58/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.58/1.59  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.59  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.58/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.58/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.58/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.58/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.59  
% 3.58/1.60  tff(f_152, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 3.58/1.60  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 3.58/1.60  tff(f_134, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 3.58/1.60  tff(f_98, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.58/1.60  tff(f_91, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 3.58/1.60  tff(f_76, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.58/1.60  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.58/1.60  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.58/1.60  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.58/1.60  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.58/1.60  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.58/1.60  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.58/1.60  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.58/1.60  tff(f_69, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.58/1.60  tff(c_94, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.58/1.60  tff(c_92, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.58/1.60  tff(c_90, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.58/1.60  tff(c_88, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.58/1.60  tff(c_86, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.58/1.60  tff(c_84, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.58/1.60  tff(c_76, plain, (![A_48, B_50]: (m1_subset_1(k6_domain_1(u1_struct_0(A_48), B_50), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_50, u1_struct_0(A_48)) | ~l1_orders_2(A_48) | ~v3_orders_2(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.58/1.60  tff(c_82, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.58/1.60  tff(c_251, plain, (![B_208, A_209, C_210]: (~r2_hidden(B_208, k1_orders_2(A_209, C_210)) | ~r2_hidden(B_208, C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(u1_struct_0(A_209))) | ~m1_subset_1(B_208, u1_struct_0(A_209)) | ~l1_orders_2(A_209) | ~v5_orders_2(A_209) | ~v4_orders_2(A_209) | ~v3_orders_2(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.58/1.60  tff(c_253, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_251])).
% 3.58/1.60  tff(c_256, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_253])).
% 3.58/1.60  tff(c_257, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_94, c_256])).
% 3.58/1.60  tff(c_336, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_257])).
% 3.58/1.60  tff(c_339, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_336])).
% 3.58/1.60  tff(c_342, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_86, c_84, c_339])).
% 3.58/1.60  tff(c_344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_342])).
% 3.58/1.60  tff(c_346, plain, (m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_257])).
% 3.58/1.60  tff(c_123, plain, (![A_68, B_69]: (k6_domain_1(A_68, B_69)=k1_tarski(B_69) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.58/1.60  tff(c_127, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_84, c_123])).
% 3.58/1.60  tff(c_128, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_127])).
% 3.58/1.60  tff(c_231, plain, (![A_188, B_189]: (m1_subset_1(k1_orders_2(A_188, B_189), k1_zfmisc_1(u1_struct_0(A_188))) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_orders_2(A_188) | ~v5_orders_2(A_188) | ~v4_orders_2(A_188) | ~v3_orders_2(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.58/1.60  tff(c_70, plain, (![C_43, B_42, A_41]: (~v1_xboole_0(C_43) | ~m1_subset_1(B_42, k1_zfmisc_1(C_43)) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.58/1.60  tff(c_407, plain, (![A_345, A_346, B_347]: (~v1_xboole_0(u1_struct_0(A_345)) | ~r2_hidden(A_346, k1_orders_2(A_345, B_347)) | ~m1_subset_1(B_347, k1_zfmisc_1(u1_struct_0(A_345))) | ~l1_orders_2(A_345) | ~v5_orders_2(A_345) | ~v4_orders_2(A_345) | ~v3_orders_2(A_345) | v2_struct_0(A_345))), inference(resolution, [status(thm)], [c_231, c_70])).
% 3.58/1.60  tff(c_409, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_407])).
% 3.58/1.60  tff(c_412, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_346, c_128, c_409])).
% 3.58/1.60  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_412])).
% 3.58/1.60  tff(c_415, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_127])).
% 3.58/1.60  tff(c_497, plain, (![A_436, B_437]: (m1_subset_1(k6_domain_1(u1_struct_0(A_436), B_437), k1_zfmisc_1(u1_struct_0(A_436))) | ~m1_subset_1(B_437, u1_struct_0(A_436)) | ~l1_orders_2(A_436) | ~v3_orders_2(A_436) | v2_struct_0(A_436))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.58/1.60  tff(c_505, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_415, c_497])).
% 3.58/1.60  tff(c_509, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_86, c_84, c_505])).
% 3.58/1.60  tff(c_510, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_94, c_509])).
% 3.58/1.60  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.58/1.60  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.58/1.60  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.60  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.58/1.60  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.58/1.60  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.58/1.60  tff(c_464, plain, (![B_435, G_433, E_431, C_430, D_434, A_429, F_432]: (k6_enumset1(A_429, A_429, B_435, C_430, D_434, E_431, F_432, G_433)=k5_enumset1(A_429, B_435, C_430, D_434, E_431, F_432, G_433))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.58/1.60  tff(c_22, plain, (![G_35, H_36, E_33, J_40, A_29, D_32, C_31, B_30]: (r2_hidden(J_40, k6_enumset1(A_29, B_30, C_31, D_32, E_33, J_40, G_35, H_36)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.58/1.60  tff(c_518, plain, (![F_442, E_439, B_440, A_441, G_438, D_443, C_444]: (r2_hidden(E_439, k5_enumset1(A_441, B_440, C_444, D_443, E_439, F_442, G_438)))), inference(superposition, [status(thm), theory('equality')], [c_464, c_22])).
% 3.58/1.60  tff(c_522, plain, (![F_445, C_450, E_447, B_446, A_448, D_449]: (r2_hidden(D_449, k4_enumset1(A_448, B_446, C_450, D_449, E_447, F_445)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_518])).
% 3.58/1.60  tff(c_526, plain, (![B_453, D_454, A_452, E_455, C_451]: (r2_hidden(C_451, k3_enumset1(A_452, B_453, C_451, D_454, E_455)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_522])).
% 3.58/1.60  tff(c_530, plain, (![B_456, A_457, C_458, D_459]: (r2_hidden(B_456, k2_enumset1(A_457, B_456, C_458, D_459)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_526])).
% 3.58/1.60  tff(c_542, plain, (![A_462, B_463, C_464]: (r2_hidden(A_462, k1_enumset1(A_462, B_463, C_464)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_530])).
% 3.58/1.60  tff(c_546, plain, (![A_465, B_466]: (r2_hidden(A_465, k2_tarski(A_465, B_466)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_542])).
% 3.58/1.60  tff(c_549, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_546])).
% 3.58/1.60  tff(c_417, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_82])).
% 3.58/1.60  tff(c_622, plain, (![B_512, A_513, C_514]: (~r2_hidden(B_512, k1_orders_2(A_513, C_514)) | ~r2_hidden(B_512, C_514) | ~m1_subset_1(C_514, k1_zfmisc_1(u1_struct_0(A_513))) | ~m1_subset_1(B_512, u1_struct_0(A_513)) | ~l1_orders_2(A_513) | ~v5_orders_2(A_513) | ~v4_orders_2(A_513) | ~v3_orders_2(A_513) | v2_struct_0(A_513))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.58/1.60  tff(c_624, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_417, c_622])).
% 3.58/1.60  tff(c_627, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_510, c_549, c_624])).
% 3.58/1.60  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_627])).
% 3.58/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.60  
% 3.58/1.60  Inference rules
% 3.58/1.60  ----------------------
% 3.58/1.60  #Ref     : 0
% 3.58/1.60  #Sup     : 116
% 3.58/1.60  #Fact    : 0
% 3.58/1.60  #Define  : 0
% 3.58/1.60  #Split   : 4
% 3.58/1.60  #Chain   : 0
% 3.58/1.60  #Close   : 0
% 3.58/1.60  
% 3.58/1.60  Ordering : KBO
% 3.58/1.60  
% 3.58/1.60  Simplification rules
% 3.58/1.60  ----------------------
% 3.58/1.60  #Subsume      : 2
% 3.58/1.60  #Demod        : 38
% 3.58/1.60  #Tautology    : 49
% 3.58/1.60  #SimpNegUnit  : 6
% 3.58/1.60  #BackRed      : 1
% 3.58/1.60  
% 3.58/1.60  #Partial instantiations: 0
% 3.58/1.60  #Strategies tried      : 1
% 3.58/1.60  
% 3.58/1.60  Timing (in seconds)
% 3.58/1.60  ----------------------
% 3.58/1.61  Preprocessing        : 0.36
% 3.58/1.61  Parsing              : 0.17
% 3.58/1.61  CNF conversion       : 0.03
% 3.58/1.61  Main loop            : 0.40
% 3.58/1.61  Inferencing          : 0.14
% 3.58/1.61  Reduction            : 0.11
% 3.58/1.61  Demodulation         : 0.08
% 3.58/1.61  BG Simplification    : 0.02
% 3.58/1.61  Subsumption          : 0.10
% 3.58/1.61  Abstraction          : 0.03
% 3.58/1.61  MUC search           : 0.00
% 3.58/1.61  Cooper               : 0.00
% 3.58/1.61  Total                : 0.79
% 3.58/1.61  Index Insertion      : 0.00
% 3.58/1.61  Index Deletion       : 0.00
% 3.58/1.61  Index Matching       : 0.00
% 3.58/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
