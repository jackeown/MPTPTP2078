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

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 224 expanded)
%              Number of leaves         :   31 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 276 expanded)
%              Number of equality atoms :   75 ( 244 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_80,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_64,axiom,(
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

tff(c_553,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k3_xboole_0(A_105,B_106)) = k4_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_565,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_553])).

tff(c_572,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_565])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_568,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_553])).

tff(c_581,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_568])).

tff(c_18,plain,(
    ! [B_18] : k4_xboole_0(k1_tarski(B_18),k1_tarski(B_18)) != k1_tarski(B_18) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_582,plain,(
    ! [B_18] : k1_tarski(B_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_18])).

tff(c_38,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_636,plain,(
    ! [A_114,B_115] :
      ( k4_xboole_0(k1_tarski(A_114),k1_tarski(B_115)) = k1_tarski(A_114)
      | B_115 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( ~ r2_hidden(B_23,A_22)
      | k4_xboole_0(A_22,k1_tarski(B_23)) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_673,plain,(
    ! [B_116,A_117] :
      ( ~ r2_hidden(B_116,k1_tarski(A_117))
      | B_116 = A_117 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_28])).

tff(c_680,plain,(
    ! [A_117] :
      ( '#skF_1'(k1_tarski(A_117)) = A_117
      | k1_tarski(A_117) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_673])).

tff(c_685,plain,(
    ! [A_117] : '#skF_1'(k1_tarski(A_117)) = A_117 ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_680])).

tff(c_605,plain,(
    ! [A_111,B_112] :
      ( k4_xboole_0(A_111,k1_tarski(B_112)) = A_111
      | r2_hidden(B_112,A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_612,plain,(
    ! [B_112] :
      ( k1_tarski(B_112) = k1_xboole_0
      | r2_hidden(B_112,k1_tarski(B_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_581])).

tff(c_627,plain,(
    ! [B_112] : r2_hidden(B_112,k1_tarski(B_112)) ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_612])).

tff(c_725,plain,(
    ! [D_125,A_126,C_127] :
      ( ~ r2_hidden(D_125,A_126)
      | k4_tarski(C_127,D_125) != '#skF_1'(A_126)
      | k1_xboole_0 = A_126 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_727,plain,(
    ! [C_127,B_112] :
      ( k4_tarski(C_127,B_112) != '#skF_1'(k1_tarski(B_112))
      | k1_tarski(B_112) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_627,c_725])).

tff(c_731,plain,(
    ! [C_127,B_112] :
      ( k4_tarski(C_127,B_112) != B_112
      | k1_tarski(B_112) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_727])).

tff(c_732,plain,(
    ! [C_127,B_112] : k4_tarski(C_127,B_112) != B_112 ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_731])).

tff(c_240,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_252,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_240])).

tff(c_259,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_252])).

tff(c_255,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_240])).

tff(c_268,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_255])).

tff(c_269,plain,(
    ! [B_18] : k1_tarski(B_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_18])).

tff(c_336,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(k1_tarski(A_78),k1_tarski(B_79)) = k1_tarski(A_78)
      | B_79 = A_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_376,plain,(
    ! [B_80,A_81] :
      ( ~ r2_hidden(B_80,k1_tarski(A_81))
      | B_80 = A_81 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_28])).

tff(c_383,plain,(
    ! [A_81] :
      ( '#skF_1'(k1_tarski(A_81)) = A_81
      | k1_tarski(A_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_376])).

tff(c_388,plain,(
    ! [A_81] : '#skF_1'(k1_tarski(A_81)) = A_81 ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_383])).

tff(c_284,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,k1_tarski(B_71)) = A_70
      | r2_hidden(B_71,A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_304,plain,(
    ! [B_71] :
      ( k1_tarski(B_71) = k1_xboole_0
      | r2_hidden(B_71,k1_tarski(B_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_284])).

tff(c_316,plain,(
    ! [B_71] : r2_hidden(B_71,k1_tarski(B_71)) ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_304])).

tff(c_412,plain,(
    ! [C_86,A_87,D_88] :
      ( ~ r2_hidden(C_86,A_87)
      | k4_tarski(C_86,D_88) != '#skF_1'(A_87)
      | k1_xboole_0 = A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_414,plain,(
    ! [B_71,D_88] :
      ( k4_tarski(B_71,D_88) != '#skF_1'(k1_tarski(B_71))
      | k1_tarski(B_71) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_316,c_412])).

tff(c_418,plain,(
    ! [B_71,D_88] :
      ( k4_tarski(B_71,D_88) != B_71
      | k1_tarski(B_71) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_414])).

tff(c_419,plain,(
    ! [B_71,D_88] : k4_tarski(B_71,D_88) != B_71 ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_418])).

tff(c_46,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_85,plain,(
    ! [A_44,B_45] : k1_mcart_1(k4_tarski(A_44,B_45)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_94,plain,(
    k1_mcart_1('#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_85])).

tff(c_69,plain,(
    ! [A_42,B_43] : k2_mcart_1(k4_tarski(A_42,B_43)) = B_43 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_78,plain,(
    k2_mcart_1('#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_69])).

tff(c_44,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_111,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_78,c_44])).

tff(c_112,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_115,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_46])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_115])).

tff(c_423,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_427,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_46])).

tff(c_735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_732,c_427])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:49:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.33  
% 2.57/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.34  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.57/1.34  
% 2.57/1.34  %Foreground sorts:
% 2.57/1.34  
% 2.57/1.34  
% 2.57/1.34  %Background operators:
% 2.57/1.34  
% 2.57/1.34  
% 2.57/1.34  %Foreground operators:
% 2.57/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.57/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.57/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.57/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.57/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.57/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.57/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.57/1.34  
% 2.57/1.35  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.57/1.35  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.57/1.35  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.57/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.57/1.35  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.57/1.35  tff(f_80, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.57/1.35  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.57/1.35  tff(f_90, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.57/1.35  tff(f_64, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.57/1.35  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.35  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.35  tff(c_553, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k3_xboole_0(A_105, B_106))=k4_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.57/1.35  tff(c_565, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_553])).
% 2.57/1.35  tff(c_572, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_565])).
% 2.57/1.35  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.57/1.35  tff(c_568, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_553])).
% 2.57/1.35  tff(c_581, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_572, c_568])).
% 2.57/1.35  tff(c_18, plain, (![B_18]: (k4_xboole_0(k1_tarski(B_18), k1_tarski(B_18))!=k1_tarski(B_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.57/1.35  tff(c_582, plain, (![B_18]: (k1_tarski(B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_581, c_18])).
% 2.57/1.35  tff(c_38, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.35  tff(c_636, plain, (![A_114, B_115]: (k4_xboole_0(k1_tarski(A_114), k1_tarski(B_115))=k1_tarski(A_114) | B_115=A_114)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.57/1.35  tff(c_28, plain, (![B_23, A_22]: (~r2_hidden(B_23, A_22) | k4_xboole_0(A_22, k1_tarski(B_23))!=A_22)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.57/1.35  tff(c_673, plain, (![B_116, A_117]: (~r2_hidden(B_116, k1_tarski(A_117)) | B_116=A_117)), inference(superposition, [status(thm), theory('equality')], [c_636, c_28])).
% 2.57/1.35  tff(c_680, plain, (![A_117]: ('#skF_1'(k1_tarski(A_117))=A_117 | k1_tarski(A_117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_673])).
% 2.57/1.35  tff(c_685, plain, (![A_117]: ('#skF_1'(k1_tarski(A_117))=A_117)), inference(negUnitSimplification, [status(thm)], [c_582, c_680])).
% 2.57/1.35  tff(c_605, plain, (![A_111, B_112]: (k4_xboole_0(A_111, k1_tarski(B_112))=A_111 | r2_hidden(B_112, A_111))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.57/1.35  tff(c_612, plain, (![B_112]: (k1_tarski(B_112)=k1_xboole_0 | r2_hidden(B_112, k1_tarski(B_112)))), inference(superposition, [status(thm), theory('equality')], [c_605, c_581])).
% 2.57/1.35  tff(c_627, plain, (![B_112]: (r2_hidden(B_112, k1_tarski(B_112)))), inference(negUnitSimplification, [status(thm)], [c_582, c_612])).
% 2.57/1.35  tff(c_725, plain, (![D_125, A_126, C_127]: (~r2_hidden(D_125, A_126) | k4_tarski(C_127, D_125)!='#skF_1'(A_126) | k1_xboole_0=A_126)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.35  tff(c_727, plain, (![C_127, B_112]: (k4_tarski(C_127, B_112)!='#skF_1'(k1_tarski(B_112)) | k1_tarski(B_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_627, c_725])).
% 2.57/1.35  tff(c_731, plain, (![C_127, B_112]: (k4_tarski(C_127, B_112)!=B_112 | k1_tarski(B_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_685, c_727])).
% 2.57/1.35  tff(c_732, plain, (![C_127, B_112]: (k4_tarski(C_127, B_112)!=B_112)), inference(negUnitSimplification, [status(thm)], [c_582, c_731])).
% 2.57/1.35  tff(c_240, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.57/1.35  tff(c_252, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_240])).
% 2.57/1.35  tff(c_259, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_252])).
% 2.57/1.35  tff(c_255, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_240])).
% 2.57/1.35  tff(c_268, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_259, c_255])).
% 2.57/1.35  tff(c_269, plain, (![B_18]: (k1_tarski(B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_268, c_18])).
% 2.57/1.35  tff(c_336, plain, (![A_78, B_79]: (k4_xboole_0(k1_tarski(A_78), k1_tarski(B_79))=k1_tarski(A_78) | B_79=A_78)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.57/1.35  tff(c_376, plain, (![B_80, A_81]: (~r2_hidden(B_80, k1_tarski(A_81)) | B_80=A_81)), inference(superposition, [status(thm), theory('equality')], [c_336, c_28])).
% 2.57/1.35  tff(c_383, plain, (![A_81]: ('#skF_1'(k1_tarski(A_81))=A_81 | k1_tarski(A_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_376])).
% 2.57/1.35  tff(c_388, plain, (![A_81]: ('#skF_1'(k1_tarski(A_81))=A_81)), inference(negUnitSimplification, [status(thm)], [c_269, c_383])).
% 2.57/1.35  tff(c_284, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k1_tarski(B_71))=A_70 | r2_hidden(B_71, A_70))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.57/1.35  tff(c_304, plain, (![B_71]: (k1_tarski(B_71)=k1_xboole_0 | r2_hidden(B_71, k1_tarski(B_71)))), inference(superposition, [status(thm), theory('equality')], [c_268, c_284])).
% 2.57/1.35  tff(c_316, plain, (![B_71]: (r2_hidden(B_71, k1_tarski(B_71)))), inference(negUnitSimplification, [status(thm)], [c_269, c_304])).
% 2.57/1.35  tff(c_412, plain, (![C_86, A_87, D_88]: (~r2_hidden(C_86, A_87) | k4_tarski(C_86, D_88)!='#skF_1'(A_87) | k1_xboole_0=A_87)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.35  tff(c_414, plain, (![B_71, D_88]: (k4_tarski(B_71, D_88)!='#skF_1'(k1_tarski(B_71)) | k1_tarski(B_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_316, c_412])).
% 2.57/1.35  tff(c_418, plain, (![B_71, D_88]: (k4_tarski(B_71, D_88)!=B_71 | k1_tarski(B_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_388, c_414])).
% 2.57/1.35  tff(c_419, plain, (![B_71, D_88]: (k4_tarski(B_71, D_88)!=B_71)), inference(negUnitSimplification, [status(thm)], [c_269, c_418])).
% 2.57/1.35  tff(c_46, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.57/1.35  tff(c_85, plain, (![A_44, B_45]: (k1_mcart_1(k4_tarski(A_44, B_45))=A_44)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.35  tff(c_94, plain, (k1_mcart_1('#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_46, c_85])).
% 2.57/1.35  tff(c_69, plain, (![A_42, B_43]: (k2_mcart_1(k4_tarski(A_42, B_43))=B_43)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.35  tff(c_78, plain, (k2_mcart_1('#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_46, c_69])).
% 2.57/1.35  tff(c_44, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.57/1.35  tff(c_111, plain, ('#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_78, c_44])).
% 2.57/1.35  tff(c_112, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_111])).
% 2.57/1.35  tff(c_115, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_46])).
% 2.57/1.35  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_419, c_115])).
% 2.57/1.35  tff(c_423, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_111])).
% 2.57/1.35  tff(c_427, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_423, c_46])).
% 2.57/1.35  tff(c_735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_732, c_427])).
% 2.57/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.35  
% 2.57/1.35  Inference rules
% 2.57/1.35  ----------------------
% 2.57/1.35  #Ref     : 0
% 2.57/1.35  #Sup     : 164
% 2.57/1.35  #Fact    : 0
% 2.57/1.35  #Define  : 0
% 2.57/1.35  #Split   : 1
% 2.57/1.35  #Chain   : 0
% 2.57/1.35  #Close   : 0
% 2.57/1.35  
% 2.57/1.35  Ordering : KBO
% 2.57/1.35  
% 2.57/1.35  Simplification rules
% 2.57/1.35  ----------------------
% 2.57/1.35  #Subsume      : 6
% 2.57/1.35  #Demod        : 37
% 2.57/1.35  #Tautology    : 130
% 2.57/1.35  #SimpNegUnit  : 16
% 2.57/1.35  #BackRed      : 10
% 2.57/1.35  
% 2.57/1.35  #Partial instantiations: 0
% 2.57/1.35  #Strategies tried      : 1
% 2.57/1.35  
% 2.57/1.35  Timing (in seconds)
% 2.57/1.35  ----------------------
% 2.57/1.36  Preprocessing        : 0.32
% 2.57/1.36  Parsing              : 0.17
% 2.57/1.36  CNF conversion       : 0.02
% 2.57/1.36  Main loop            : 0.26
% 2.57/1.36  Inferencing          : 0.10
% 2.57/1.36  Reduction            : 0.08
% 2.57/1.36  Demodulation         : 0.06
% 2.57/1.36  BG Simplification    : 0.02
% 2.57/1.36  Subsumption          : 0.04
% 2.57/1.36  Abstraction          : 0.02
% 2.57/1.36  MUC search           : 0.00
% 2.57/1.36  Cooper               : 0.00
% 2.57/1.36  Total                : 0.62
% 2.57/1.36  Index Insertion      : 0.00
% 2.57/1.36  Index Deletion       : 0.00
% 2.57/1.36  Index Matching       : 0.00
% 2.57/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
