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
% DateTime   : Thu Dec  3 10:09:18 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 249 expanded)
%              Number of leaves         :   32 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 330 expanded)
%              Number of equality atoms :   74 ( 276 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_505,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_517,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_505])).

tff(c_524,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_517])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_520,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_505])).

tff(c_533,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_520])).

tff(c_20,plain,(
    ! [B_22] : k4_xboole_0(k1_tarski(B_22),k1_tarski(B_22)) != k1_tarski(B_22) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_534,plain,(
    ! [B_22] : k1_tarski(B_22) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_20])).

tff(c_36,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_564,plain,(
    ! [A_111,B_112] :
      ( k4_xboole_0(k1_tarski(A_111),k1_tarski(B_112)) = k1_tarski(A_111)
      | B_112 = A_111 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [C_25,B_24] : ~ r2_hidden(C_25,k4_xboole_0(B_24,k1_tarski(C_25))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_591,plain,(
    ! [B_113,A_114] :
      ( ~ r2_hidden(B_113,k1_tarski(A_114))
      | B_113 = A_114 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_26])).

tff(c_595,plain,(
    ! [A_114] :
      ( '#skF_1'(k1_tarski(A_114)) = A_114
      | k1_tarski(A_114) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_591])).

tff(c_598,plain,(
    ! [A_114] : '#skF_1'(k1_tarski(A_114)) = A_114 ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_595])).

tff(c_608,plain,(
    ! [A_118] : '#skF_1'(k1_tarski(A_118)) = A_118 ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_595])).

tff(c_614,plain,(
    ! [A_118] :
      ( r2_hidden(A_118,k1_tarski(A_118))
      | k1_tarski(A_118) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_36])).

tff(c_619,plain,(
    ! [A_118] : r2_hidden(A_118,k1_tarski(A_118)) ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_614])).

tff(c_627,plain,(
    ! [D_120,A_121,C_122] :
      ( ~ r2_hidden(D_120,A_121)
      | k4_tarski(C_122,D_120) != '#skF_1'(A_121)
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_629,plain,(
    ! [C_122,A_118] :
      ( k4_tarski(C_122,A_118) != '#skF_1'(k1_tarski(A_118))
      | k1_tarski(A_118) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_619,c_627])).

tff(c_633,plain,(
    ! [C_122,A_118] :
      ( k4_tarski(C_122,A_118) != A_118
      | k1_tarski(A_118) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_629])).

tff(c_634,plain,(
    ! [C_122,A_118] : k4_tarski(C_122,A_118) != A_118 ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_633])).

tff(c_237,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_249,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_237])).

tff(c_256,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_249])).

tff(c_252,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_237])).

tff(c_284,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_252])).

tff(c_285,plain,(
    ! [B_22] : k1_tarski(B_22) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_20])).

tff(c_258,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(k1_tarski(A_68),k1_tarski(B_69)) = k1_tarski(A_68)
      | B_69 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_323,plain,(
    ! [B_77,A_78] :
      ( ~ r2_hidden(B_77,k1_tarski(A_78))
      | B_77 = A_78 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_26])).

tff(c_327,plain,(
    ! [A_78] :
      ( '#skF_1'(k1_tarski(A_78)) = A_78
      | k1_tarski(A_78) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_323])).

tff(c_330,plain,(
    ! [A_78] : '#skF_1'(k1_tarski(A_78)) = A_78 ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_327])).

tff(c_331,plain,(
    ! [A_79] : '#skF_1'(k1_tarski(A_79)) = A_79 ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_327])).

tff(c_337,plain,(
    ! [A_79] :
      ( r2_hidden(A_79,k1_tarski(A_79))
      | k1_tarski(A_79) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_36])).

tff(c_342,plain,(
    ! [A_79] : r2_hidden(A_79,k1_tarski(A_79)) ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_337])).

tff(c_363,plain,(
    ! [C_84,A_85,D_86] :
      ( ~ r2_hidden(C_84,A_85)
      | k4_tarski(C_84,D_86) != '#skF_1'(A_85)
      | k1_xboole_0 = A_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_365,plain,(
    ! [A_79,D_86] :
      ( k4_tarski(A_79,D_86) != '#skF_1'(k1_tarski(A_79))
      | k1_tarski(A_79) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_342,c_363])).

tff(c_369,plain,(
    ! [A_79,D_86] :
      ( k4_tarski(A_79,D_86) != A_79
      | k1_tarski(A_79) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_365])).

tff(c_370,plain,(
    ! [A_79,D_86] : k4_tarski(A_79,D_86) != A_79 ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_369])).

tff(c_44,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_83,plain,(
    ! [A_46,B_47] : k1_mcart_1(k4_tarski(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92,plain,(
    k1_mcart_1('#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_83])).

tff(c_67,plain,(
    ! [A_44,B_45] : k2_mcart_1(k4_tarski(A_44,B_45)) = B_45 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    k2_mcart_1('#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_67])).

tff(c_42,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_107,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_76,c_42])).

tff(c_108,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_111,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_44])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_111])).

tff(c_374,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_378,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_44])).

tff(c_646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_634,c_378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.35  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.51/1.35  
% 2.51/1.35  %Foreground sorts:
% 2.51/1.35  
% 2.51/1.35  
% 2.51/1.35  %Background operators:
% 2.51/1.35  
% 2.51/1.35  
% 2.51/1.35  %Foreground operators:
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.51/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.35  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.51/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.51/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.35  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.51/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.51/1.35  
% 2.51/1.37  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.51/1.37  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.51/1.37  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.51/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.51/1.37  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.51/1.37  tff(f_77, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.51/1.37  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.51/1.37  tff(f_87, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.51/1.37  tff(f_61, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.51/1.37  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.37  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.37  tff(c_505, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.37  tff(c_517, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_505])).
% 2.51/1.37  tff(c_524, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_517])).
% 2.51/1.37  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.37  tff(c_520, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_505])).
% 2.51/1.37  tff(c_533, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_524, c_520])).
% 2.51/1.37  tff(c_20, plain, (![B_22]: (k4_xboole_0(k1_tarski(B_22), k1_tarski(B_22))!=k1_tarski(B_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.37  tff(c_534, plain, (![B_22]: (k1_tarski(B_22)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_533, c_20])).
% 2.51/1.37  tff(c_36, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.51/1.37  tff(c_564, plain, (![A_111, B_112]: (k4_xboole_0(k1_tarski(A_111), k1_tarski(B_112))=k1_tarski(A_111) | B_112=A_111)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.37  tff(c_26, plain, (![C_25, B_24]: (~r2_hidden(C_25, k4_xboole_0(B_24, k1_tarski(C_25))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.51/1.37  tff(c_591, plain, (![B_113, A_114]: (~r2_hidden(B_113, k1_tarski(A_114)) | B_113=A_114)), inference(superposition, [status(thm), theory('equality')], [c_564, c_26])).
% 2.51/1.37  tff(c_595, plain, (![A_114]: ('#skF_1'(k1_tarski(A_114))=A_114 | k1_tarski(A_114)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_591])).
% 2.51/1.37  tff(c_598, plain, (![A_114]: ('#skF_1'(k1_tarski(A_114))=A_114)), inference(negUnitSimplification, [status(thm)], [c_534, c_595])).
% 2.51/1.37  tff(c_608, plain, (![A_118]: ('#skF_1'(k1_tarski(A_118))=A_118)), inference(negUnitSimplification, [status(thm)], [c_534, c_595])).
% 2.51/1.37  tff(c_614, plain, (![A_118]: (r2_hidden(A_118, k1_tarski(A_118)) | k1_tarski(A_118)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_608, c_36])).
% 2.51/1.37  tff(c_619, plain, (![A_118]: (r2_hidden(A_118, k1_tarski(A_118)))), inference(negUnitSimplification, [status(thm)], [c_534, c_614])).
% 2.51/1.37  tff(c_627, plain, (![D_120, A_121, C_122]: (~r2_hidden(D_120, A_121) | k4_tarski(C_122, D_120)!='#skF_1'(A_121) | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.51/1.37  tff(c_629, plain, (![C_122, A_118]: (k4_tarski(C_122, A_118)!='#skF_1'(k1_tarski(A_118)) | k1_tarski(A_118)=k1_xboole_0)), inference(resolution, [status(thm)], [c_619, c_627])).
% 2.51/1.37  tff(c_633, plain, (![C_122, A_118]: (k4_tarski(C_122, A_118)!=A_118 | k1_tarski(A_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_598, c_629])).
% 2.51/1.37  tff(c_634, plain, (![C_122, A_118]: (k4_tarski(C_122, A_118)!=A_118)), inference(negUnitSimplification, [status(thm)], [c_534, c_633])).
% 2.51/1.37  tff(c_237, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.37  tff(c_249, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_237])).
% 2.51/1.37  tff(c_256, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_249])).
% 2.51/1.37  tff(c_252, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_237])).
% 2.51/1.37  tff(c_284, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_252])).
% 2.51/1.37  tff(c_285, plain, (![B_22]: (k1_tarski(B_22)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_284, c_20])).
% 2.51/1.37  tff(c_258, plain, (![A_68, B_69]: (k4_xboole_0(k1_tarski(A_68), k1_tarski(B_69))=k1_tarski(A_68) | B_69=A_68)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.37  tff(c_323, plain, (![B_77, A_78]: (~r2_hidden(B_77, k1_tarski(A_78)) | B_77=A_78)), inference(superposition, [status(thm), theory('equality')], [c_258, c_26])).
% 2.51/1.37  tff(c_327, plain, (![A_78]: ('#skF_1'(k1_tarski(A_78))=A_78 | k1_tarski(A_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_323])).
% 2.51/1.37  tff(c_330, plain, (![A_78]: ('#skF_1'(k1_tarski(A_78))=A_78)), inference(negUnitSimplification, [status(thm)], [c_285, c_327])).
% 2.51/1.37  tff(c_331, plain, (![A_79]: ('#skF_1'(k1_tarski(A_79))=A_79)), inference(negUnitSimplification, [status(thm)], [c_285, c_327])).
% 2.51/1.37  tff(c_337, plain, (![A_79]: (r2_hidden(A_79, k1_tarski(A_79)) | k1_tarski(A_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_331, c_36])).
% 2.51/1.37  tff(c_342, plain, (![A_79]: (r2_hidden(A_79, k1_tarski(A_79)))), inference(negUnitSimplification, [status(thm)], [c_285, c_337])).
% 2.51/1.37  tff(c_363, plain, (![C_84, A_85, D_86]: (~r2_hidden(C_84, A_85) | k4_tarski(C_84, D_86)!='#skF_1'(A_85) | k1_xboole_0=A_85)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.51/1.37  tff(c_365, plain, (![A_79, D_86]: (k4_tarski(A_79, D_86)!='#skF_1'(k1_tarski(A_79)) | k1_tarski(A_79)=k1_xboole_0)), inference(resolution, [status(thm)], [c_342, c_363])).
% 2.51/1.37  tff(c_369, plain, (![A_79, D_86]: (k4_tarski(A_79, D_86)!=A_79 | k1_tarski(A_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_330, c_365])).
% 2.51/1.37  tff(c_370, plain, (![A_79, D_86]: (k4_tarski(A_79, D_86)!=A_79)), inference(negUnitSimplification, [status(thm)], [c_285, c_369])).
% 2.51/1.37  tff(c_44, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.37  tff(c_83, plain, (![A_46, B_47]: (k1_mcart_1(k4_tarski(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.51/1.37  tff(c_92, plain, (k1_mcart_1('#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_44, c_83])).
% 2.51/1.37  tff(c_67, plain, (![A_44, B_45]: (k2_mcart_1(k4_tarski(A_44, B_45))=B_45)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.51/1.37  tff(c_76, plain, (k2_mcart_1('#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_44, c_67])).
% 2.51/1.37  tff(c_42, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.37  tff(c_107, plain, ('#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_76, c_42])).
% 2.51/1.37  tff(c_108, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_107])).
% 2.51/1.37  tff(c_111, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_44])).
% 2.51/1.37  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_111])).
% 2.51/1.37  tff(c_374, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_107])).
% 2.51/1.37  tff(c_378, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_374, c_44])).
% 2.51/1.37  tff(c_646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_634, c_378])).
% 2.51/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.37  
% 2.51/1.37  Inference rules
% 2.51/1.37  ----------------------
% 2.51/1.37  #Ref     : 0
% 2.51/1.37  #Sup     : 145
% 2.51/1.37  #Fact    : 0
% 2.51/1.37  #Define  : 0
% 2.51/1.37  #Split   : 1
% 2.51/1.37  #Chain   : 0
% 2.51/1.37  #Close   : 0
% 2.51/1.37  
% 2.51/1.37  Ordering : KBO
% 2.51/1.37  
% 2.51/1.37  Simplification rules
% 2.51/1.37  ----------------------
% 2.51/1.37  #Subsume      : 2
% 2.51/1.37  #Demod        : 32
% 2.51/1.37  #Tautology    : 113
% 2.51/1.37  #SimpNegUnit  : 11
% 2.51/1.37  #BackRed      : 10
% 2.51/1.37  
% 2.51/1.37  #Partial instantiations: 0
% 2.51/1.37  #Strategies tried      : 1
% 2.51/1.37  
% 2.51/1.37  Timing (in seconds)
% 2.51/1.37  ----------------------
% 2.51/1.37  Preprocessing        : 0.33
% 2.51/1.37  Parsing              : 0.17
% 2.51/1.37  CNF conversion       : 0.02
% 2.51/1.37  Main loop            : 0.27
% 2.51/1.37  Inferencing          : 0.11
% 2.51/1.37  Reduction            : 0.08
% 2.51/1.37  Demodulation         : 0.06
% 2.51/1.37  BG Simplification    : 0.02
% 2.51/1.37  Subsumption          : 0.03
% 2.51/1.37  Abstraction          : 0.02
% 2.51/1.37  MUC search           : 0.00
% 2.51/1.37  Cooper               : 0.00
% 2.51/1.37  Total                : 0.64
% 2.51/1.37  Index Insertion      : 0.00
% 2.51/1.37  Index Deletion       : 0.00
% 2.51/1.37  Index Matching       : 0.00
% 2.51/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
