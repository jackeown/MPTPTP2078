%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:10 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 140 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 200 expanded)
%              Number of equality atoms :   63 ( 154 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_34,plain,(
    ! [C_16] : r2_hidden(C_16,k1_tarski(C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_494,plain,(
    ! [A_111,B_112] : k4_xboole_0(A_111,k4_xboole_0(A_111,B_112)) = k3_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_512,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_494])).

tff(c_516,plain,(
    ! [A_113] : k4_xboole_0(A_113,A_113) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_512])).

tff(c_50,plain,(
    ! [B_24,A_23] :
      ( ~ r2_hidden(B_24,A_23)
      | k4_xboole_0(A_23,k1_tarski(B_24)) != A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_525,plain,(
    ! [B_24] :
      ( ~ r2_hidden(B_24,k1_tarski(B_24))
      | k1_tarski(B_24) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_50])).

tff(c_547,plain,(
    ! [B_24] : k1_tarski(B_24) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_525])).

tff(c_58,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_5'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_426,plain,(
    ! [C_98,A_99] :
      ( C_98 = A_99
      | ~ r2_hidden(C_98,k1_tarski(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_434,plain,(
    ! [A_99] :
      ( '#skF_5'(k1_tarski(A_99)) = A_99
      | k1_tarski(A_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_426])).

tff(c_553,plain,(
    ! [A_99] : '#skF_5'(k1_tarski(A_99)) = A_99 ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_434])).

tff(c_597,plain,(
    ! [D_120,A_121,C_122] :
      ( ~ r2_hidden(D_120,A_121)
      | k4_tarski(C_122,D_120) != '#skF_5'(A_121)
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_611,plain,(
    ! [C_122,C_16] :
      ( k4_tarski(C_122,C_16) != '#skF_5'(k1_tarski(C_16))
      | k1_tarski(C_16) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_597])).

tff(c_619,plain,(
    ! [C_122,C_16] :
      ( k4_tarski(C_122,C_16) != C_16
      | k1_tarski(C_16) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_611])).

tff(c_620,plain,(
    ! [C_122,C_16] : k4_tarski(C_122,C_16) != C_16 ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_619])).

tff(c_186,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k4_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_201,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_186])).

tff(c_204,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_201])).

tff(c_256,plain,(
    ! [B_69,A_70] :
      ( ~ r2_hidden(B_69,A_70)
      | k4_xboole_0(A_70,k1_tarski(B_69)) != A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_260,plain,(
    ! [B_69] :
      ( ~ r2_hidden(B_69,k1_tarski(B_69))
      | k1_tarski(B_69) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_256])).

tff(c_262,plain,(
    ! [B_69] : k1_tarski(B_69) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_260])).

tff(c_157,plain,(
    ! [C_57,A_58] :
      ( C_57 = A_58
      | ~ r2_hidden(C_57,k1_tarski(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_165,plain,(
    ! [A_58] :
      ( '#skF_5'(k1_tarski(A_58)) = A_58
      | k1_tarski(A_58) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_157])).

tff(c_264,plain,(
    ! [A_58] : '#skF_5'(k1_tarski(A_58)) = A_58 ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_165])).

tff(c_366,plain,(
    ! [C_85,A_86,D_87] :
      ( ~ r2_hidden(C_85,A_86)
      | k4_tarski(C_85,D_87) != '#skF_5'(A_86)
      | k1_xboole_0 = A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_380,plain,(
    ! [C_16,D_87] :
      ( k4_tarski(C_16,D_87) != '#skF_5'(k1_tarski(C_16))
      | k1_tarski(C_16) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_366])).

tff(c_388,plain,(
    ! [C_16,D_87] :
      ( k4_tarski(C_16,D_87) != C_16
      | k1_tarski(C_16) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_380])).

tff(c_389,plain,(
    ! [C_16,D_87] : k4_tarski(C_16,D_87) != C_16 ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_388])).

tff(c_66,plain,(
    k4_tarski('#skF_7','#skF_8') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_113,plain,(
    ! [A_45,B_46] : k1_mcart_1(k4_tarski(A_45,B_46)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_122,plain,(
    k1_mcart_1('#skF_6') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_113])).

tff(c_88,plain,(
    ! [A_42,B_43] : k2_mcart_1(k4_tarski(A_42,B_43)) = B_43 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_97,plain,(
    k2_mcart_1('#skF_6') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_88])).

tff(c_64,plain,
    ( k2_mcart_1('#skF_6') = '#skF_6'
    | k1_mcart_1('#skF_6') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_129,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_97,c_64])).

tff(c_130,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_132,plain,(
    k4_tarski('#skF_6','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_66])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_132])).

tff(c_392,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_396,plain,(
    k4_tarski('#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_66])).

tff(c_622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_620,c_396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:35:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.36  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 2.61/1.36  
% 2.61/1.36  %Foreground sorts:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Background operators:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Foreground operators:
% 2.61/1.36  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.61/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.61/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.61/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.36  tff('#skF_8', type, '#skF_8': $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.36  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.36  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.61/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.61/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.61/1.36  
% 2.61/1.38  tff(f_53, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.61/1.38  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.61/1.38  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.61/1.38  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.61/1.38  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.61/1.38  tff(f_84, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.61/1.38  tff(f_94, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.61/1.38  tff(f_68, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.61/1.38  tff(c_34, plain, (![C_16]: (r2_hidden(C_16, k1_tarski(C_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.38  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.61/1.38  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.38  tff(c_494, plain, (![A_111, B_112]: (k4_xboole_0(A_111, k4_xboole_0(A_111, B_112))=k3_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.38  tff(c_512, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_494])).
% 2.61/1.38  tff(c_516, plain, (![A_113]: (k4_xboole_0(A_113, A_113)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_512])).
% 2.61/1.38  tff(c_50, plain, (![B_24, A_23]: (~r2_hidden(B_24, A_23) | k4_xboole_0(A_23, k1_tarski(B_24))!=A_23)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.61/1.38  tff(c_525, plain, (![B_24]: (~r2_hidden(B_24, k1_tarski(B_24)) | k1_tarski(B_24)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_516, c_50])).
% 2.61/1.38  tff(c_547, plain, (![B_24]: (k1_tarski(B_24)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_525])).
% 2.61/1.38  tff(c_58, plain, (![A_27]: (r2_hidden('#skF_5'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.61/1.38  tff(c_426, plain, (![C_98, A_99]: (C_98=A_99 | ~r2_hidden(C_98, k1_tarski(A_99)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.38  tff(c_434, plain, (![A_99]: ('#skF_5'(k1_tarski(A_99))=A_99 | k1_tarski(A_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_426])).
% 2.61/1.38  tff(c_553, plain, (![A_99]: ('#skF_5'(k1_tarski(A_99))=A_99)), inference(negUnitSimplification, [status(thm)], [c_547, c_434])).
% 2.61/1.38  tff(c_597, plain, (![D_120, A_121, C_122]: (~r2_hidden(D_120, A_121) | k4_tarski(C_122, D_120)!='#skF_5'(A_121) | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.61/1.38  tff(c_611, plain, (![C_122, C_16]: (k4_tarski(C_122, C_16)!='#skF_5'(k1_tarski(C_16)) | k1_tarski(C_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_597])).
% 2.61/1.38  tff(c_619, plain, (![C_122, C_16]: (k4_tarski(C_122, C_16)!=C_16 | k1_tarski(C_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_553, c_611])).
% 2.61/1.38  tff(c_620, plain, (![C_122, C_16]: (k4_tarski(C_122, C_16)!=C_16)), inference(negUnitSimplification, [status(thm)], [c_547, c_619])).
% 2.61/1.38  tff(c_186, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k4_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.38  tff(c_201, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_186])).
% 2.61/1.38  tff(c_204, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_201])).
% 2.61/1.38  tff(c_256, plain, (![B_69, A_70]: (~r2_hidden(B_69, A_70) | k4_xboole_0(A_70, k1_tarski(B_69))!=A_70)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.61/1.38  tff(c_260, plain, (![B_69]: (~r2_hidden(B_69, k1_tarski(B_69)) | k1_tarski(B_69)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_204, c_256])).
% 2.61/1.38  tff(c_262, plain, (![B_69]: (k1_tarski(B_69)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_260])).
% 2.61/1.38  tff(c_157, plain, (![C_57, A_58]: (C_57=A_58 | ~r2_hidden(C_57, k1_tarski(A_58)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.38  tff(c_165, plain, (![A_58]: ('#skF_5'(k1_tarski(A_58))=A_58 | k1_tarski(A_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_157])).
% 2.61/1.38  tff(c_264, plain, (![A_58]: ('#skF_5'(k1_tarski(A_58))=A_58)), inference(negUnitSimplification, [status(thm)], [c_262, c_165])).
% 2.61/1.38  tff(c_366, plain, (![C_85, A_86, D_87]: (~r2_hidden(C_85, A_86) | k4_tarski(C_85, D_87)!='#skF_5'(A_86) | k1_xboole_0=A_86)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.61/1.38  tff(c_380, plain, (![C_16, D_87]: (k4_tarski(C_16, D_87)!='#skF_5'(k1_tarski(C_16)) | k1_tarski(C_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_366])).
% 2.61/1.38  tff(c_388, plain, (![C_16, D_87]: (k4_tarski(C_16, D_87)!=C_16 | k1_tarski(C_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_264, c_380])).
% 2.61/1.38  tff(c_389, plain, (![C_16, D_87]: (k4_tarski(C_16, D_87)!=C_16)), inference(negUnitSimplification, [status(thm)], [c_262, c_388])).
% 2.61/1.38  tff(c_66, plain, (k4_tarski('#skF_7', '#skF_8')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.61/1.38  tff(c_113, plain, (![A_45, B_46]: (k1_mcart_1(k4_tarski(A_45, B_46))=A_45)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.38  tff(c_122, plain, (k1_mcart_1('#skF_6')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_66, c_113])).
% 2.61/1.38  tff(c_88, plain, (![A_42, B_43]: (k2_mcart_1(k4_tarski(A_42, B_43))=B_43)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.38  tff(c_97, plain, (k2_mcart_1('#skF_6')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_66, c_88])).
% 2.61/1.38  tff(c_64, plain, (k2_mcart_1('#skF_6')='#skF_6' | k1_mcart_1('#skF_6')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.61/1.38  tff(c_129, plain, ('#skF_6'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_97, c_64])).
% 2.61/1.38  tff(c_130, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_129])).
% 2.61/1.38  tff(c_132, plain, (k4_tarski('#skF_6', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_66])).
% 2.61/1.38  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_389, c_132])).
% 2.61/1.38  tff(c_392, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_129])).
% 2.61/1.38  tff(c_396, plain, (k4_tarski('#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_392, c_66])).
% 2.61/1.38  tff(c_622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_620, c_396])).
% 2.61/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.38  
% 2.61/1.38  Inference rules
% 2.61/1.38  ----------------------
% 2.61/1.38  #Ref     : 0
% 2.61/1.38  #Sup     : 135
% 2.61/1.38  #Fact    : 0
% 2.61/1.38  #Define  : 0
% 2.61/1.38  #Split   : 1
% 2.61/1.38  #Chain   : 0
% 2.61/1.38  #Close   : 0
% 2.61/1.38  
% 2.61/1.38  Ordering : KBO
% 2.61/1.38  
% 2.61/1.38  Simplification rules
% 2.61/1.38  ----------------------
% 2.61/1.38  #Subsume      : 1
% 2.61/1.38  #Demod        : 37
% 2.61/1.38  #Tautology    : 93
% 2.61/1.38  #SimpNegUnit  : 13
% 2.61/1.38  #BackRed      : 8
% 2.61/1.38  
% 2.61/1.38  #Partial instantiations: 0
% 2.61/1.38  #Strategies tried      : 1
% 2.61/1.38  
% 2.61/1.38  Timing (in seconds)
% 2.61/1.38  ----------------------
% 2.61/1.38  Preprocessing        : 0.33
% 2.61/1.38  Parsing              : 0.16
% 2.61/1.38  CNF conversion       : 0.03
% 2.61/1.38  Main loop            : 0.27
% 2.61/1.38  Inferencing          : 0.10
% 2.61/1.38  Reduction            : 0.09
% 2.61/1.38  Demodulation         : 0.06
% 2.61/1.38  BG Simplification    : 0.02
% 2.61/1.38  Subsumption          : 0.04
% 2.61/1.38  Abstraction          : 0.02
% 2.61/1.38  MUC search           : 0.00
% 2.61/1.38  Cooper               : 0.00
% 2.61/1.38  Total                : 0.64
% 2.61/1.38  Index Insertion      : 0.00
% 2.61/1.38  Index Deletion       : 0.00
% 2.61/1.38  Index Matching       : 0.00
% 2.61/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
