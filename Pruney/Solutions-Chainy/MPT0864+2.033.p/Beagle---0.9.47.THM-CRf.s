%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:13 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 150 expanded)
%              Number of leaves         :   33 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 189 expanded)
%              Number of equality atoms :   70 ( 163 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_523,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k3_xboole_0(A_103,B_104)) = k4_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_535,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_523])).

tff(c_539,plain,(
    ! [A_105] : k4_xboole_0(A_105,k1_xboole_0) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_535])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_545,plain,(
    ! [A_105] : k4_xboole_0(A_105,A_105) = k3_xboole_0(A_105,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_8])).

tff(c_550,plain,(
    ! [A_105] : k4_xboole_0(A_105,A_105) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_545])).

tff(c_34,plain,(
    ! [B_30] : k4_xboole_0(k1_tarski(B_30),k1_tarski(B_30)) != k1_tarski(B_30) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_552,plain,(
    ! [B_30] : k1_tarski(B_30) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_34])).

tff(c_456,plain,(
    ! [A_93] :
      ( r2_hidden('#skF_3'(A_93),A_93)
      | k1_xboole_0 = A_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_461,plain,(
    ! [A_9] :
      ( '#skF_3'(k1_tarski(A_9)) = A_9
      | k1_tarski(A_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_456,c_12])).

tff(c_574,plain,(
    ! [A_9] : '#skF_3'(k1_tarski(A_9)) = A_9 ),
    inference(negUnitSimplification,[status(thm)],[c_552,c_461])).

tff(c_14,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_670,plain,(
    ! [D_117,A_118,C_119] :
      ( ~ r2_hidden(D_117,A_118)
      | k4_tarski(C_119,D_117) != '#skF_3'(A_118)
      | k1_xboole_0 = A_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_674,plain,(
    ! [C_119,C_13] :
      ( k4_tarski(C_119,C_13) != '#skF_3'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_670])).

tff(c_677,plain,(
    ! [C_119,C_13] :
      ( k4_tarski(C_119,C_13) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_674])).

tff(c_678,plain,(
    ! [C_119,C_13] : k4_tarski(C_119,C_13) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_552,c_677])).

tff(c_193,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_205,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_193])).

tff(c_208,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_205])).

tff(c_260,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_275,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_260])).

tff(c_278,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_275])).

tff(c_289,plain,(
    ! [B_30] : k1_tarski(B_30) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_34])).

tff(c_44,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_3'(A_35),A_35)
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_159,plain,(
    ! [C_57,A_58] :
      ( C_57 = A_58
      | ~ r2_hidden(C_57,k1_tarski(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_167,plain,(
    ! [A_58] :
      ( '#skF_3'(k1_tarski(A_58)) = A_58
      | k1_tarski(A_58) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_159])).

tff(c_311,plain,(
    ! [A_58] : '#skF_3'(k1_tarski(A_58)) = A_58 ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_167])).

tff(c_410,plain,(
    ! [C_88,A_89,D_90] :
      ( ~ r2_hidden(C_88,A_89)
      | k4_tarski(C_88,D_90) != '#skF_3'(A_89)
      | k1_xboole_0 = A_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_414,plain,(
    ! [C_13,D_90] :
      ( k4_tarski(C_13,D_90) != '#skF_3'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_410])).

tff(c_417,plain,(
    ! [C_13,D_90] :
      ( k4_tarski(C_13,D_90) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_414])).

tff(c_418,plain,(
    ! [C_13,D_90] : k4_tarski(C_13,D_90) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_417])).

tff(c_52,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_93,plain,(
    ! [A_51,B_52] : k2_mcart_1(k4_tarski(A_51,B_52)) = B_52 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_102,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_93])).

tff(c_50,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_130,plain,
    ( '#skF_6' = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_50])).

tff(c_131,plain,(
    k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_118,plain,(
    ! [A_54,B_55] : k1_mcart_1(k4_tarski(A_54,B_55)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_127,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_118])).

tff(c_136,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_127])).

tff(c_141,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_52])).

tff(c_420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_141])).

tff(c_421,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_424,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_52])).

tff(c_680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_678,c_424])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.81  
% 3.14/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.81  %$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.14/1.81  
% 3.14/1.81  %Foreground sorts:
% 3.14/1.81  
% 3.14/1.81  
% 3.14/1.81  %Background operators:
% 3.14/1.81  
% 3.14/1.81  
% 3.14/1.81  %Foreground operators:
% 3.14/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.14/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.14/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.81  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.81  tff('#skF_6', type, '#skF_6': $i).
% 3.14/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.81  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.14/1.81  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.81  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.14/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.14/1.81  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.14/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.14/1.81  
% 3.14/1.84  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.14/1.84  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.14/1.84  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.14/1.84  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.14/1.84  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.14/1.84  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.14/1.84  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.14/1.84  tff(f_89, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.14/1.84  tff(f_63, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.14/1.84  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.84  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.84  tff(c_523, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k3_xboole_0(A_103, B_104))=k4_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.84  tff(c_535, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_523])).
% 3.14/1.84  tff(c_539, plain, (![A_105]: (k4_xboole_0(A_105, k1_xboole_0)=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_535])).
% 3.14/1.84  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.14/1.84  tff(c_545, plain, (![A_105]: (k4_xboole_0(A_105, A_105)=k3_xboole_0(A_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_539, c_8])).
% 3.14/1.84  tff(c_550, plain, (![A_105]: (k4_xboole_0(A_105, A_105)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_545])).
% 3.14/1.84  tff(c_34, plain, (![B_30]: (k4_xboole_0(k1_tarski(B_30), k1_tarski(B_30))!=k1_tarski(B_30))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.14/1.84  tff(c_552, plain, (![B_30]: (k1_tarski(B_30)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_550, c_34])).
% 3.14/1.84  tff(c_456, plain, (![A_93]: (r2_hidden('#skF_3'(A_93), A_93) | k1_xboole_0=A_93)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.14/1.84  tff(c_12, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.14/1.84  tff(c_461, plain, (![A_9]: ('#skF_3'(k1_tarski(A_9))=A_9 | k1_tarski(A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_456, c_12])).
% 3.14/1.84  tff(c_574, plain, (![A_9]: ('#skF_3'(k1_tarski(A_9))=A_9)), inference(negUnitSimplification, [status(thm)], [c_552, c_461])).
% 3.14/1.84  tff(c_14, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.14/1.84  tff(c_670, plain, (![D_117, A_118, C_119]: (~r2_hidden(D_117, A_118) | k4_tarski(C_119, D_117)!='#skF_3'(A_118) | k1_xboole_0=A_118)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.14/1.84  tff(c_674, plain, (![C_119, C_13]: (k4_tarski(C_119, C_13)!='#skF_3'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_670])).
% 3.14/1.84  tff(c_677, plain, (![C_119, C_13]: (k4_tarski(C_119, C_13)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_574, c_674])).
% 3.14/1.84  tff(c_678, plain, (![C_119, C_13]: (k4_tarski(C_119, C_13)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_552, c_677])).
% 3.14/1.84  tff(c_193, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.84  tff(c_205, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_193])).
% 3.14/1.84  tff(c_208, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_205])).
% 3.14/1.84  tff(c_260, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.14/1.84  tff(c_275, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_208, c_260])).
% 3.14/1.84  tff(c_278, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_275])).
% 3.14/1.84  tff(c_289, plain, (![B_30]: (k1_tarski(B_30)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_278, c_34])).
% 3.14/1.84  tff(c_44, plain, (![A_35]: (r2_hidden('#skF_3'(A_35), A_35) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.14/1.84  tff(c_159, plain, (![C_57, A_58]: (C_57=A_58 | ~r2_hidden(C_57, k1_tarski(A_58)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.14/1.84  tff(c_167, plain, (![A_58]: ('#skF_3'(k1_tarski(A_58))=A_58 | k1_tarski(A_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_159])).
% 3.14/1.84  tff(c_311, plain, (![A_58]: ('#skF_3'(k1_tarski(A_58))=A_58)), inference(negUnitSimplification, [status(thm)], [c_289, c_167])).
% 3.14/1.84  tff(c_410, plain, (![C_88, A_89, D_90]: (~r2_hidden(C_88, A_89) | k4_tarski(C_88, D_90)!='#skF_3'(A_89) | k1_xboole_0=A_89)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.14/1.84  tff(c_414, plain, (![C_13, D_90]: (k4_tarski(C_13, D_90)!='#skF_3'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_410])).
% 3.14/1.84  tff(c_417, plain, (![C_13, D_90]: (k4_tarski(C_13, D_90)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_311, c_414])).
% 3.14/1.84  tff(c_418, plain, (![C_13, D_90]: (k4_tarski(C_13, D_90)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_289, c_417])).
% 3.14/1.84  tff(c_52, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.14/1.84  tff(c_93, plain, (![A_51, B_52]: (k2_mcart_1(k4_tarski(A_51, B_52))=B_52)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.84  tff(c_102, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_52, c_93])).
% 3.14/1.84  tff(c_50, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.14/1.84  tff(c_130, plain, ('#skF_6'='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_50])).
% 3.14/1.84  tff(c_131, plain, (k1_mcart_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_130])).
% 3.14/1.84  tff(c_118, plain, (![A_54, B_55]: (k1_mcart_1(k4_tarski(A_54, B_55))=A_54)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.84  tff(c_127, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_52, c_118])).
% 3.14/1.84  tff(c_136, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_127])).
% 3.14/1.84  tff(c_141, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_52])).
% 3.14/1.84  tff(c_420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_418, c_141])).
% 3.14/1.84  tff(c_421, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_130])).
% 3.14/1.84  tff(c_424, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_421, c_52])).
% 3.14/1.84  tff(c_680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_678, c_424])).
% 3.14/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.84  
% 3.14/1.84  Inference rules
% 3.14/1.84  ----------------------
% 3.14/1.84  #Ref     : 0
% 3.14/1.84  #Sup     : 145
% 3.14/1.84  #Fact    : 0
% 3.14/1.84  #Define  : 0
% 3.14/1.84  #Split   : 1
% 3.14/1.84  #Chain   : 0
% 3.14/1.84  #Close   : 0
% 3.14/1.84  
% 3.14/1.84  Ordering : KBO
% 3.14/1.84  
% 3.14/1.84  Simplification rules
% 3.14/1.84  ----------------------
% 3.14/1.84  #Subsume      : 2
% 3.14/1.84  #Demod        : 37
% 3.14/1.84  #Tautology    : 118
% 3.14/1.84  #SimpNegUnit  : 17
% 3.14/1.84  #BackRed      : 11
% 3.14/1.84  
% 3.14/1.84  #Partial instantiations: 0
% 3.14/1.84  #Strategies tried      : 1
% 3.14/1.84  
% 3.14/1.84  Timing (in seconds)
% 3.14/1.84  ----------------------
% 3.14/1.84  Preprocessing        : 0.52
% 3.14/1.84  Parsing              : 0.27
% 3.14/1.84  CNF conversion       : 0.04
% 3.14/1.84  Main loop            : 0.41
% 3.14/1.84  Inferencing          : 0.16
% 3.14/1.84  Reduction            : 0.13
% 3.14/1.84  Demodulation         : 0.09
% 3.14/1.84  BG Simplification    : 0.03
% 3.14/1.84  Subsumption          : 0.06
% 3.14/1.84  Abstraction          : 0.03
% 3.14/1.84  MUC search           : 0.00
% 3.14/1.84  Cooper               : 0.00
% 3.14/1.84  Total                : 0.98
% 3.14/1.84  Index Insertion      : 0.00
% 3.14/1.84  Index Deletion       : 0.00
% 3.14/1.84  Index Matching       : 0.00
% 3.14/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
