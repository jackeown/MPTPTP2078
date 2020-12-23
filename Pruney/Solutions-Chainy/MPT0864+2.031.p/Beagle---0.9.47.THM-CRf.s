%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:12 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 157 expanded)
%              Number of leaves         :   36 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 196 expanded)
%              Number of equality atoms :   67 ( 170 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_65,axiom,(
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

tff(c_516,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_528,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_516])).

tff(c_535,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_528])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_531,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_516])).

tff(c_544,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_531])).

tff(c_36,plain,(
    ! [B_38] : k4_xboole_0(k1_tarski(B_38),k1_tarski(B_38)) != k1_tarski(B_38) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_545,plain,(
    ! [B_38] : k1_tarski(B_38) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_36])).

tff(c_46,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_3'(A_43),A_43)
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_398,plain,(
    ! [C_101,A_102] :
      ( C_101 = A_102
      | ~ r2_hidden(C_101,k1_tarski(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_406,plain,(
    ! [A_102] :
      ( '#skF_3'(k1_tarski(A_102)) = A_102
      | k1_tarski(A_102) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_398])).

tff(c_574,plain,(
    ! [A_102] : '#skF_3'(k1_tarski(A_102)) = A_102 ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_406])).

tff(c_12,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_611,plain,(
    ! [D_134,A_135,C_136] :
      ( ~ r2_hidden(D_134,A_135)
      | k4_tarski(C_136,D_134) != '#skF_3'(A_135)
      | k1_xboole_0 = A_135 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_615,plain,(
    ! [C_136,C_13] :
      ( k4_tarski(C_136,C_13) != '#skF_3'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_611])).

tff(c_618,plain,(
    ! [C_136,C_13] :
      ( k4_tarski(C_136,C_13) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_615])).

tff(c_619,plain,(
    ! [C_136,C_13] : k4_tarski(C_136,C_13) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_618])).

tff(c_267,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_279,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_267])).

tff(c_286,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_279])).

tff(c_282,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_267])).

tff(c_295,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_282])).

tff(c_296,plain,(
    ! [B_38] : k1_tarski(B_38) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_36])).

tff(c_151,plain,(
    ! [C_67,A_68] :
      ( C_67 = A_68
      | ~ r2_hidden(C_67,k1_tarski(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_159,plain,(
    ! [A_68] :
      ( '#skF_3'(k1_tarski(A_68)) = A_68
      | k1_tarski(A_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_151])).

tff(c_324,plain,(
    ! [A_68] : '#skF_3'(k1_tarski(A_68)) = A_68 ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_159])).

tff(c_362,plain,(
    ! [C_97,A_98,D_99] :
      ( ~ r2_hidden(C_97,A_98)
      | k4_tarski(C_97,D_99) != '#skF_3'(A_98)
      | k1_xboole_0 = A_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_366,plain,(
    ! [C_13,D_99] :
      ( k4_tarski(C_13,D_99) != '#skF_3'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_362])).

tff(c_369,plain,(
    ! [C_13,D_99] :
      ( k4_tarski(C_13,D_99) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_366])).

tff(c_370,plain,(
    ! [C_13,D_99] : k4_tarski(C_13,D_99) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_369])).

tff(c_54,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_90,plain,(
    ! [A_60,B_61] : k1_mcart_1(k4_tarski(A_60,B_61)) = A_60 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_99,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_90])).

tff(c_78,plain,(
    ! [A_58,B_59] : k2_mcart_1(k4_tarski(A_58,B_59)) = B_59 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_87,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_78])).

tff(c_52,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_110,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_87,c_52])).

tff(c_111,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_113,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_54])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_113])).

tff(c_373,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_376,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_54])).

tff(c_621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_619,c_376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.40  
% 2.54/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.41  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.54/1.41  
% 2.54/1.41  %Foreground sorts:
% 2.54/1.41  
% 2.54/1.41  
% 2.54/1.41  %Background operators:
% 2.54/1.41  
% 2.54/1.41  
% 2.54/1.41  %Foreground operators:
% 2.54/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.54/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.54/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.54/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.41  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.54/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.54/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.54/1.41  
% 2.67/1.42  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.67/1.42  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.67/1.42  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.67/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.67/1.42  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.67/1.42  tff(f_81, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.67/1.42  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.67/1.42  tff(f_91, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.67/1.42  tff(f_65, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.67/1.42  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.42  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.42  tff(c_516, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.42  tff(c_528, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_516])).
% 2.67/1.42  tff(c_535, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_528])).
% 2.67/1.42  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.42  tff(c_531, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_516])).
% 2.67/1.42  tff(c_544, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_535, c_531])).
% 2.67/1.42  tff(c_36, plain, (![B_38]: (k4_xboole_0(k1_tarski(B_38), k1_tarski(B_38))!=k1_tarski(B_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.42  tff(c_545, plain, (![B_38]: (k1_tarski(B_38)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_544, c_36])).
% 2.67/1.42  tff(c_46, plain, (![A_43]: (r2_hidden('#skF_3'(A_43), A_43) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.42  tff(c_398, plain, (![C_101, A_102]: (C_101=A_102 | ~r2_hidden(C_101, k1_tarski(A_102)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.42  tff(c_406, plain, (![A_102]: ('#skF_3'(k1_tarski(A_102))=A_102 | k1_tarski(A_102)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_398])).
% 2.67/1.42  tff(c_574, plain, (![A_102]: ('#skF_3'(k1_tarski(A_102))=A_102)), inference(negUnitSimplification, [status(thm)], [c_545, c_406])).
% 2.67/1.42  tff(c_12, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.42  tff(c_611, plain, (![D_134, A_135, C_136]: (~r2_hidden(D_134, A_135) | k4_tarski(C_136, D_134)!='#skF_3'(A_135) | k1_xboole_0=A_135)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.42  tff(c_615, plain, (![C_136, C_13]: (k4_tarski(C_136, C_13)!='#skF_3'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_611])).
% 2.67/1.42  tff(c_618, plain, (![C_136, C_13]: (k4_tarski(C_136, C_13)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_574, c_615])).
% 2.67/1.42  tff(c_619, plain, (![C_136, C_13]: (k4_tarski(C_136, C_13)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_545, c_618])).
% 2.67/1.42  tff(c_267, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.42  tff(c_279, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_267])).
% 2.67/1.42  tff(c_286, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_279])).
% 2.67/1.42  tff(c_282, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_267])).
% 2.67/1.42  tff(c_295, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_282])).
% 2.67/1.42  tff(c_296, plain, (![B_38]: (k1_tarski(B_38)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_295, c_36])).
% 2.67/1.42  tff(c_151, plain, (![C_67, A_68]: (C_67=A_68 | ~r2_hidden(C_67, k1_tarski(A_68)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.42  tff(c_159, plain, (![A_68]: ('#skF_3'(k1_tarski(A_68))=A_68 | k1_tarski(A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_151])).
% 2.67/1.42  tff(c_324, plain, (![A_68]: ('#skF_3'(k1_tarski(A_68))=A_68)), inference(negUnitSimplification, [status(thm)], [c_296, c_159])).
% 2.67/1.42  tff(c_362, plain, (![C_97, A_98, D_99]: (~r2_hidden(C_97, A_98) | k4_tarski(C_97, D_99)!='#skF_3'(A_98) | k1_xboole_0=A_98)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.42  tff(c_366, plain, (![C_13, D_99]: (k4_tarski(C_13, D_99)!='#skF_3'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_362])).
% 2.67/1.42  tff(c_369, plain, (![C_13, D_99]: (k4_tarski(C_13, D_99)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_324, c_366])).
% 2.67/1.42  tff(c_370, plain, (![C_13, D_99]: (k4_tarski(C_13, D_99)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_296, c_369])).
% 2.67/1.42  tff(c_54, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.67/1.42  tff(c_90, plain, (![A_60, B_61]: (k1_mcart_1(k4_tarski(A_60, B_61))=A_60)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.67/1.42  tff(c_99, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_54, c_90])).
% 2.67/1.42  tff(c_78, plain, (![A_58, B_59]: (k2_mcart_1(k4_tarski(A_58, B_59))=B_59)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.67/1.42  tff(c_87, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_54, c_78])).
% 2.67/1.42  tff(c_52, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.67/1.42  tff(c_110, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_87, c_52])).
% 2.67/1.42  tff(c_111, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_110])).
% 2.67/1.42  tff(c_113, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_54])).
% 2.67/1.42  tff(c_372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_113])).
% 2.67/1.42  tff(c_373, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_110])).
% 2.67/1.42  tff(c_376, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_373, c_54])).
% 2.67/1.42  tff(c_621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_619, c_376])).
% 2.67/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.42  
% 2.67/1.42  Inference rules
% 2.67/1.42  ----------------------
% 2.67/1.42  #Ref     : 0
% 2.67/1.42  #Sup     : 137
% 2.67/1.42  #Fact    : 0
% 2.67/1.42  #Define  : 0
% 2.67/1.42  #Split   : 1
% 2.67/1.42  #Chain   : 0
% 2.67/1.42  #Close   : 0
% 2.67/1.42  
% 2.67/1.42  Ordering : KBO
% 2.67/1.42  
% 2.67/1.42  Simplification rules
% 2.67/1.42  ----------------------
% 2.67/1.42  #Subsume      : 1
% 2.67/1.42  #Demod        : 33
% 2.67/1.42  #Tautology    : 111
% 2.67/1.42  #SimpNegUnit  : 10
% 2.67/1.42  #BackRed      : 9
% 2.67/1.42  
% 2.67/1.42  #Partial instantiations: 0
% 2.67/1.42  #Strategies tried      : 1
% 2.67/1.42  
% 2.67/1.42  Timing (in seconds)
% 2.67/1.42  ----------------------
% 2.67/1.42  Preprocessing        : 0.38
% 2.67/1.42  Parsing              : 0.19
% 2.67/1.42  CNF conversion       : 0.03
% 2.67/1.42  Main loop            : 0.25
% 2.67/1.42  Inferencing          : 0.10
% 2.67/1.42  Reduction            : 0.07
% 2.67/1.42  Demodulation         : 0.05
% 2.67/1.43  BG Simplification    : 0.02
% 2.67/1.43  Subsumption          : 0.03
% 2.67/1.43  Abstraction          : 0.02
% 2.67/1.43  MUC search           : 0.00
% 2.67/1.43  Cooper               : 0.00
% 2.67/1.43  Total                : 0.66
% 2.67/1.43  Index Insertion      : 0.00
% 2.67/1.43  Index Deletion       : 0.00
% 2.67/1.43  Index Matching       : 0.00
% 2.67/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
