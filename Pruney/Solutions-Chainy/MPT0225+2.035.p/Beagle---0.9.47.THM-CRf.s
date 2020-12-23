%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:35 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 171 expanded)
%              Number of leaves         :   29 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 217 expanded)
%              Number of equality atoms :   55 ( 166 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_511,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = k1_xboole_0
      | ~ r1_xboole_0(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_519,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_511])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_568,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k4_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_583,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_568])).

tff(c_586,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_583])).

tff(c_340,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = k1_xboole_0
      | ~ r1_xboole_0(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_352,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_340])).

tff(c_386,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_404,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_386])).

tff(c_407,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_404])).

tff(c_40,plain,
    ( '#skF_3' != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_96,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_116,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_116])).

tff(c_128,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_125])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(k1_tarski(A_24),B_25)
      | r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_220,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(k1_tarski(A_54),B_55) = k1_xboole_0
      | r2_hidden(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_34,c_96])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_230,plain,(
    ! [A_54,B_55] :
      ( k5_xboole_0(k1_tarski(A_54),k1_xboole_0) = k4_xboole_0(k1_tarski(A_54),B_55)
      | r2_hidden(A_54,B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_6])).

tff(c_264,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(k1_tarski(A_59),B_60) = k1_tarski(A_59)
      | r2_hidden(A_59,B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_230])).

tff(c_38,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_305,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_80])).

tff(c_14,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_313,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_305,c_14])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_313])).

tff(c_318,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_319,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_409,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_318,c_319,c_42])).

tff(c_418,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_409])).

tff(c_334,plain,(
    ! [A_63,B_64] :
      ( r1_xboole_0(A_63,B_64)
      | k3_xboole_0(A_63,B_64) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [B_27] : ~ r1_xboole_0(k1_tarski(B_27),k1_tarski(B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_338,plain,(
    ! [B_27] : k3_xboole_0(k1_tarski(B_27),k1_tarski(B_27)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_334,c_36])).

tff(c_443,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_6')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_338])).

tff(c_466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_418,c_443])).

tff(c_467,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_468,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( '#skF_3' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_588,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_467,c_468,c_44])).

tff(c_597,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_588])).

tff(c_527,plain,(
    ! [A_86,B_87] :
      ( r1_xboole_0(A_86,B_87)
      | k3_xboole_0(A_86,B_87) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_535,plain,(
    ! [B_27] : k3_xboole_0(k1_tarski(B_27),k1_tarski(B_27)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_527,c_36])).

tff(c_622,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_6')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_535])).

tff(c_645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_597,c_622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.31  
% 2.23/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.31  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.23/1.31  
% 2.23/1.31  %Foreground sorts:
% 2.23/1.31  
% 2.23/1.31  
% 2.23/1.31  %Background operators:
% 2.23/1.31  
% 2.23/1.31  
% 2.23/1.31  %Foreground operators:
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.31  
% 2.23/1.33  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.23/1.33  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.23/1.33  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.23/1.33  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.23/1.33  tff(f_68, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.23/1.33  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.23/1.33  tff(f_57, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.23/1.33  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.23/1.33  tff(f_62, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.23/1.33  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.33  tff(c_511, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=k1_xboole_0 | ~r1_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.33  tff(c_519, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_511])).
% 2.23/1.33  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.33  tff(c_568, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k4_xboole_0(A_94, B_95))=k3_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.33  tff(c_583, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_568])).
% 2.23/1.33  tff(c_586, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_519, c_583])).
% 2.23/1.33  tff(c_340, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=k1_xboole_0 | ~r1_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.33  tff(c_352, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_340])).
% 2.23/1.33  tff(c_386, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k4_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.33  tff(c_404, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_386])).
% 2.23/1.33  tff(c_407, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_352, c_404])).
% 2.23/1.33  tff(c_40, plain, ('#skF_3'!='#skF_4' | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.33  tff(c_46, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_40])).
% 2.23/1.33  tff(c_96, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.33  tff(c_108, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_96])).
% 2.23/1.33  tff(c_116, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.33  tff(c_125, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_108, c_116])).
% 2.23/1.33  tff(c_128, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_125])).
% 2.23/1.33  tff(c_34, plain, (![A_24, B_25]: (r1_xboole_0(k1_tarski(A_24), B_25) | r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.23/1.33  tff(c_220, plain, (![A_54, B_55]: (k3_xboole_0(k1_tarski(A_54), B_55)=k1_xboole_0 | r2_hidden(A_54, B_55))), inference(resolution, [status(thm)], [c_34, c_96])).
% 2.23/1.33  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.33  tff(c_230, plain, (![A_54, B_55]: (k5_xboole_0(k1_tarski(A_54), k1_xboole_0)=k4_xboole_0(k1_tarski(A_54), B_55) | r2_hidden(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_220, c_6])).
% 2.23/1.33  tff(c_264, plain, (![A_59, B_60]: (k4_xboole_0(k1_tarski(A_59), B_60)=k1_tarski(A_59) | r2_hidden(A_59, B_60))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_230])).
% 2.23/1.33  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.33  tff(c_80, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 2.23/1.33  tff(c_305, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_264, c_80])).
% 2.23/1.33  tff(c_14, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.23/1.33  tff(c_313, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_305, c_14])).
% 2.23/1.33  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_313])).
% 2.23/1.33  tff(c_318, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 2.23/1.33  tff(c_319, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 2.23/1.33  tff(c_42, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.33  tff(c_409, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_318, c_319, c_42])).
% 2.23/1.33  tff(c_418, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_407, c_409])).
% 2.23/1.33  tff(c_334, plain, (![A_63, B_64]: (r1_xboole_0(A_63, B_64) | k3_xboole_0(A_63, B_64)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.33  tff(c_36, plain, (![B_27]: (~r1_xboole_0(k1_tarski(B_27), k1_tarski(B_27)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.33  tff(c_338, plain, (![B_27]: (k3_xboole_0(k1_tarski(B_27), k1_tarski(B_27))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_334, c_36])).
% 2.23/1.33  tff(c_443, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_6'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_418, c_338])).
% 2.23/1.33  tff(c_466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_352, c_418, c_443])).
% 2.23/1.33  tff(c_467, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_40])).
% 2.23/1.33  tff(c_468, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 2.23/1.33  tff(c_44, plain, ('#skF_3'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.33  tff(c_588, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_467, c_467, c_468, c_44])).
% 2.23/1.33  tff(c_597, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_586, c_588])).
% 2.23/1.33  tff(c_527, plain, (![A_86, B_87]: (r1_xboole_0(A_86, B_87) | k3_xboole_0(A_86, B_87)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.33  tff(c_535, plain, (![B_27]: (k3_xboole_0(k1_tarski(B_27), k1_tarski(B_27))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_527, c_36])).
% 2.23/1.33  tff(c_622, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_6'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_597, c_535])).
% 2.23/1.33  tff(c_645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_519, c_597, c_622])).
% 2.23/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.33  
% 2.23/1.33  Inference rules
% 2.23/1.33  ----------------------
% 2.23/1.33  #Ref     : 0
% 2.23/1.33  #Sup     : 143
% 2.23/1.33  #Fact    : 0
% 2.23/1.33  #Define  : 0
% 2.23/1.33  #Split   : 2
% 2.23/1.33  #Chain   : 0
% 2.23/1.33  #Close   : 0
% 2.23/1.33  
% 2.23/1.33  Ordering : KBO
% 2.23/1.33  
% 2.23/1.33  Simplification rules
% 2.23/1.33  ----------------------
% 2.23/1.33  #Subsume      : 3
% 2.23/1.33  #Demod        : 38
% 2.23/1.33  #Tautology    : 94
% 2.23/1.33  #SimpNegUnit  : 5
% 2.23/1.33  #BackRed      : 3
% 2.23/1.33  
% 2.23/1.33  #Partial instantiations: 0
% 2.23/1.33  #Strategies tried      : 1
% 2.23/1.33  
% 2.23/1.33  Timing (in seconds)
% 2.23/1.33  ----------------------
% 2.23/1.33  Preprocessing        : 0.30
% 2.23/1.33  Parsing              : 0.16
% 2.23/1.33  CNF conversion       : 0.02
% 2.23/1.33  Main loop            : 0.23
% 2.23/1.33  Inferencing          : 0.09
% 2.23/1.33  Reduction            : 0.07
% 2.23/1.33  Demodulation         : 0.05
% 2.23/1.33  BG Simplification    : 0.01
% 2.23/1.33  Subsumption          : 0.03
% 2.23/1.33  Abstraction          : 0.01
% 2.23/1.33  MUC search           : 0.00
% 2.23/1.33  Cooper               : 0.00
% 2.23/1.33  Total                : 0.56
% 2.23/1.33  Index Insertion      : 0.00
% 2.23/1.33  Index Deletion       : 0.00
% 2.23/1.33  Index Matching       : 0.00
% 2.23/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
