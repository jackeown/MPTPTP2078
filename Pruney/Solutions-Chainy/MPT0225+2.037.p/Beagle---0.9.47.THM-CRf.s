%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:35 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   63 (  81 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   62 (  99 expanded)
%              Number of equality atoms :   30 (  59 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_18,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_242,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,k3_xboole_0(A_86,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_246,plain,(
    ! [A_89,C_90] :
      ( ~ r1_xboole_0(A_89,A_89)
      | ~ r2_hidden(C_90,A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_242])).

tff(c_256,plain,(
    ! [C_91,B_92] :
      ( ~ r2_hidden(C_91,B_92)
      | k4_xboole_0(B_92,B_92) != B_92 ) ),
    inference(resolution,[status(thm)],[c_14,c_246])).

tff(c_259,plain,(
    ! [C_18] : k4_xboole_0(k1_tarski(C_18),k1_tarski(C_18)) != k1_tarski(C_18) ),
    inference(resolution,[status(thm)],[c_18,c_256])).

tff(c_46,plain,
    ( '#skF_5' != '#skF_4'
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_51,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_89,plain,(
    ! [A_60,B_61] :
      ( r1_xboole_0(k1_tarski(A_60),B_61)
      | r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_173,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(k1_tarski(A_80),B_81) = k1_tarski(A_80)
      | r2_hidden(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_89,c_12])).

tff(c_44,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_88,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_197,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_88])).

tff(c_16,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_203,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_197,c_16])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_203])).

tff(c_209,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_210,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_347,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_210,c_48])).

tff(c_348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_347])).

tff(c_349,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_350,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( '#skF_5' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_436,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_350,c_50])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_440,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_10])).

tff(c_431,plain,(
    ! [A_122,B_123,C_124] :
      ( ~ r1_xboole_0(A_122,B_123)
      | ~ r2_hidden(C_124,k3_xboole_0(A_122,B_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_449,plain,(
    ! [A_125,C_126] :
      ( ~ r1_xboole_0(A_125,A_125)
      | ~ r2_hidden(C_126,A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_431])).

tff(c_462,plain,(
    ! [C_127] : ~ r2_hidden(C_127,k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_440,c_449])).

tff(c_467,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.31  
% 2.31/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.31  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.31/1.31  
% 2.31/1.31  %Foreground sorts:
% 2.31/1.31  
% 2.31/1.31  
% 2.31/1.31  %Background operators:
% 2.31/1.31  
% 2.31/1.31  
% 2.31/1.31  %Foreground operators:
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.31/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.31/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.31/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.31/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.31/1.31  
% 2.31/1.32  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.31/1.32  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.31/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.31/1.32  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.31/1.32  tff(f_81, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.31/1.32  tff(f_75, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.31/1.32  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.31/1.32  tff(c_18, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.31/1.32  tff(c_14, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.32  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.32  tff(c_242, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, k3_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.32  tff(c_246, plain, (![A_89, C_90]: (~r1_xboole_0(A_89, A_89) | ~r2_hidden(C_90, A_89))), inference(superposition, [status(thm), theory('equality')], [c_2, c_242])).
% 2.31/1.32  tff(c_256, plain, (![C_91, B_92]: (~r2_hidden(C_91, B_92) | k4_xboole_0(B_92, B_92)!=B_92)), inference(resolution, [status(thm)], [c_14, c_246])).
% 2.31/1.32  tff(c_259, plain, (![C_18]: (k4_xboole_0(k1_tarski(C_18), k1_tarski(C_18))!=k1_tarski(C_18))), inference(resolution, [status(thm)], [c_18, c_256])).
% 2.31/1.32  tff(c_46, plain, ('#skF_5'!='#skF_4' | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.32  tff(c_51, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_46])).
% 2.31/1.32  tff(c_89, plain, (![A_60, B_61]: (r1_xboole_0(k1_tarski(A_60), B_61) | r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.32  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.32  tff(c_173, plain, (![A_80, B_81]: (k4_xboole_0(k1_tarski(A_80), B_81)=k1_tarski(A_80) | r2_hidden(A_80, B_81))), inference(resolution, [status(thm)], [c_89, c_12])).
% 2.31/1.32  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.32  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 2.31/1.32  tff(c_197, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_173, c_88])).
% 2.31/1.32  tff(c_16, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.31/1.32  tff(c_203, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_197, c_16])).
% 2.31/1.32  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_203])).
% 2.31/1.32  tff(c_209, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 2.31/1.32  tff(c_210, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 2.31/1.32  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.32  tff(c_347, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_210, c_48])).
% 2.31/1.32  tff(c_348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_347])).
% 2.31/1.32  tff(c_349, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 2.31/1.32  tff(c_350, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.31/1.32  tff(c_50, plain, ('#skF_5'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.32  tff(c_436, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_349, c_350, c_50])).
% 2.31/1.32  tff(c_10, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.31/1.32  tff(c_440, plain, (r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_436, c_10])).
% 2.31/1.32  tff(c_431, plain, (![A_122, B_123, C_124]: (~r1_xboole_0(A_122, B_123) | ~r2_hidden(C_124, k3_xboole_0(A_122, B_123)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.32  tff(c_449, plain, (![A_125, C_126]: (~r1_xboole_0(A_125, A_125) | ~r2_hidden(C_126, A_125))), inference(superposition, [status(thm), theory('equality')], [c_2, c_431])).
% 2.31/1.32  tff(c_462, plain, (![C_127]: (~r2_hidden(C_127, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_440, c_449])).
% 2.31/1.32  tff(c_467, plain, $false, inference(resolution, [status(thm)], [c_18, c_462])).
% 2.31/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.32  
% 2.31/1.32  Inference rules
% 2.31/1.32  ----------------------
% 2.31/1.32  #Ref     : 0
% 2.31/1.32  #Sup     : 95
% 2.31/1.32  #Fact    : 0
% 2.31/1.32  #Define  : 0
% 2.31/1.32  #Split   : 2
% 2.31/1.32  #Chain   : 0
% 2.31/1.32  #Close   : 0
% 2.31/1.32  
% 2.31/1.32  Ordering : KBO
% 2.31/1.32  
% 2.31/1.32  Simplification rules
% 2.31/1.32  ----------------------
% 2.31/1.32  #Subsume      : 5
% 2.31/1.32  #Demod        : 26
% 2.31/1.32  #Tautology    : 71
% 2.31/1.32  #SimpNegUnit  : 2
% 2.31/1.32  #BackRed      : 0
% 2.31/1.32  
% 2.31/1.33  #Partial instantiations: 0
% 2.31/1.33  #Strategies tried      : 1
% 2.31/1.33  
% 2.31/1.33  Timing (in seconds)
% 2.31/1.33  ----------------------
% 2.31/1.33  Preprocessing        : 0.31
% 2.31/1.33  Parsing              : 0.16
% 2.31/1.33  CNF conversion       : 0.02
% 2.31/1.33  Main loop            : 0.20
% 2.31/1.33  Inferencing          : 0.08
% 2.31/1.33  Reduction            : 0.06
% 2.31/1.33  Demodulation         : 0.04
% 2.31/1.33  BG Simplification    : 0.02
% 2.31/1.33  Subsumption          : 0.03
% 2.31/1.33  Abstraction          : 0.01
% 2.31/1.33  MUC search           : 0.00
% 2.31/1.33  Cooper               : 0.00
% 2.31/1.33  Total                : 0.55
% 2.31/1.33  Index Insertion      : 0.00
% 2.31/1.33  Index Deletion       : 0.00
% 2.31/1.33  Index Matching       : 0.00
% 2.31/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
