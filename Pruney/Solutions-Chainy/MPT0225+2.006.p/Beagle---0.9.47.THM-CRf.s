%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:31 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   64 (  85 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   71 ( 116 expanded)
%              Number of equality atoms :   36 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(c_24,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_494,plain,(
    ! [A_112,B_113] :
      ( k3_xboole_0(A_112,B_113) = A_112
      | ~ r1_tarski(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_498,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_12,c_494])).

tff(c_526,plain,(
    ! [A_121,B_122,C_123] :
      ( ~ r1_xboole_0(A_121,B_122)
      | ~ r2_hidden(C_123,k3_xboole_0(A_121,B_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_554,plain,(
    ! [B_126,C_127] :
      ( ~ r1_xboole_0(B_126,B_126)
      | ~ r2_hidden(C_127,B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_526])).

tff(c_573,plain,(
    ! [C_129,B_130] :
      ( ~ r2_hidden(C_129,B_130)
      | k4_xboole_0(B_130,B_130) != B_130 ) ),
    inference(resolution,[status(thm)],[c_20,c_554])).

tff(c_576,plain,(
    ! [C_20] : k4_xboole_0(k1_tarski(C_20),k1_tarski(C_20)) != k1_tarski(C_20) ),
    inference(resolution,[status(thm)],[c_24,c_573])).

tff(c_293,plain,(
    ! [A_78,B_79] :
      ( k3_xboole_0(A_78,B_79) = A_78
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_297,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_12,c_293])).

tff(c_311,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r1_xboole_0(A_81,B_82)
      | ~ r2_hidden(C_83,k3_xboole_0(A_81,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_321,plain,(
    ! [B_84,C_85] :
      ( ~ r1_xboole_0(B_84,B_84)
      | ~ r2_hidden(C_85,B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_311])).

tff(c_332,plain,(
    ! [C_86,B_87] :
      ( ~ r2_hidden(C_86,B_87)
      | k4_xboole_0(B_87,B_87) != B_87 ) ),
    inference(resolution,[status(thm)],[c_20,c_321])).

tff(c_335,plain,(
    ! [C_20] : k4_xboole_0(k1_tarski(C_20),k1_tarski(C_20)) != k1_tarski(C_20) ),
    inference(resolution,[status(thm)],[c_24,c_332])).

tff(c_46,plain,
    ( '#skF_5' != '#skF_4'
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_53,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    ! [A_31,B_32] :
      ( r1_xboole_0(k1_tarski(A_31),B_32)
      | r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_115,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = A_46
      | ~ r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_248,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(k1_tarski(A_72),B_73) = k1_tarski(A_72)
      | r2_hidden(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_42,c_115])).

tff(c_44,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_113,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_265,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_113])).

tff(c_22,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_271,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_265,c_22])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_271])).

tff(c_277,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_278,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_423,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_278,c_48])).

tff(c_424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_335,c_423])).

tff(c_425,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_426,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( '#skF_5' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_578,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_426,c_50])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_576,c_578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:42:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.37  
% 2.61/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.61/1.38  
% 2.61/1.38  %Foreground sorts:
% 2.61/1.38  
% 2.61/1.38  
% 2.61/1.38  %Background operators:
% 2.61/1.38  
% 2.61/1.38  
% 2.61/1.38  %Foreground operators:
% 2.61/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.61/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.61/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.38  
% 2.61/1.39  tff(f_64, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.61/1.39  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.61/1.39  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.39  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.61/1.39  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.61/1.39  tff(f_83, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.61/1.39  tff(f_77, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.61/1.39  tff(c_24, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.61/1.39  tff(c_20, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.39  tff(c_12, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.39  tff(c_494, plain, (![A_112, B_113]: (k3_xboole_0(A_112, B_113)=A_112 | ~r1_tarski(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.39  tff(c_498, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_12, c_494])).
% 2.61/1.39  tff(c_526, plain, (![A_121, B_122, C_123]: (~r1_xboole_0(A_121, B_122) | ~r2_hidden(C_123, k3_xboole_0(A_121, B_122)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.61/1.39  tff(c_554, plain, (![B_126, C_127]: (~r1_xboole_0(B_126, B_126) | ~r2_hidden(C_127, B_126))), inference(superposition, [status(thm), theory('equality')], [c_498, c_526])).
% 2.61/1.39  tff(c_573, plain, (![C_129, B_130]: (~r2_hidden(C_129, B_130) | k4_xboole_0(B_130, B_130)!=B_130)), inference(resolution, [status(thm)], [c_20, c_554])).
% 2.61/1.39  tff(c_576, plain, (![C_20]: (k4_xboole_0(k1_tarski(C_20), k1_tarski(C_20))!=k1_tarski(C_20))), inference(resolution, [status(thm)], [c_24, c_573])).
% 2.61/1.39  tff(c_293, plain, (![A_78, B_79]: (k3_xboole_0(A_78, B_79)=A_78 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.39  tff(c_297, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_12, c_293])).
% 2.61/1.39  tff(c_311, plain, (![A_81, B_82, C_83]: (~r1_xboole_0(A_81, B_82) | ~r2_hidden(C_83, k3_xboole_0(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.61/1.39  tff(c_321, plain, (![B_84, C_85]: (~r1_xboole_0(B_84, B_84) | ~r2_hidden(C_85, B_84))), inference(superposition, [status(thm), theory('equality')], [c_297, c_311])).
% 2.61/1.39  tff(c_332, plain, (![C_86, B_87]: (~r2_hidden(C_86, B_87) | k4_xboole_0(B_87, B_87)!=B_87)), inference(resolution, [status(thm)], [c_20, c_321])).
% 2.61/1.39  tff(c_335, plain, (![C_20]: (k4_xboole_0(k1_tarski(C_20), k1_tarski(C_20))!=k1_tarski(C_20))), inference(resolution, [status(thm)], [c_24, c_332])).
% 2.61/1.39  tff(c_46, plain, ('#skF_5'!='#skF_4' | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.61/1.39  tff(c_53, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_46])).
% 2.61/1.39  tff(c_42, plain, (![A_31, B_32]: (r1_xboole_0(k1_tarski(A_31), B_32) | r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.39  tff(c_115, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=A_46 | ~r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.39  tff(c_248, plain, (![A_72, B_73]: (k4_xboole_0(k1_tarski(A_72), B_73)=k1_tarski(A_72) | r2_hidden(A_72, B_73))), inference(resolution, [status(thm)], [c_42, c_115])).
% 2.61/1.39  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.61/1.39  tff(c_113, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 2.61/1.39  tff(c_265, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_113])).
% 2.61/1.39  tff(c_22, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.61/1.39  tff(c_271, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_265, c_22])).
% 2.61/1.39  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_271])).
% 2.61/1.39  tff(c_277, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 2.61/1.39  tff(c_278, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 2.61/1.39  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.61/1.39  tff(c_423, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_278, c_48])).
% 2.61/1.39  tff(c_424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_335, c_423])).
% 2.61/1.39  tff(c_425, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 2.61/1.39  tff(c_426, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.61/1.39  tff(c_50, plain, ('#skF_5'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.61/1.39  tff(c_578, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_425, c_426, c_50])).
% 2.61/1.39  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_576, c_578])).
% 2.61/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.39  
% 2.61/1.39  Inference rules
% 2.61/1.39  ----------------------
% 2.61/1.39  #Ref     : 0
% 2.61/1.39  #Sup     : 123
% 2.61/1.39  #Fact    : 0
% 2.61/1.39  #Define  : 0
% 2.61/1.39  #Split   : 2
% 2.61/1.39  #Chain   : 0
% 2.61/1.39  #Close   : 0
% 2.61/1.39  
% 2.61/1.39  Ordering : KBO
% 2.61/1.39  
% 2.61/1.39  Simplification rules
% 2.61/1.39  ----------------------
% 2.61/1.39  #Subsume      : 11
% 2.61/1.39  #Demod        : 23
% 2.61/1.39  #Tautology    : 88
% 2.61/1.39  #SimpNegUnit  : 3
% 2.61/1.39  #BackRed      : 1
% 2.61/1.39  
% 2.61/1.39  #Partial instantiations: 0
% 2.61/1.39  #Strategies tried      : 1
% 2.61/1.39  
% 2.61/1.39  Timing (in seconds)
% 2.61/1.39  ----------------------
% 2.61/1.39  Preprocessing        : 0.33
% 2.61/1.39  Parsing              : 0.17
% 2.61/1.39  CNF conversion       : 0.02
% 2.61/1.39  Main loop            : 0.25
% 2.61/1.39  Inferencing          : 0.10
% 2.61/1.39  Reduction            : 0.08
% 2.61/1.39  Demodulation         : 0.06
% 2.61/1.39  BG Simplification    : 0.02
% 2.61/1.39  Subsumption          : 0.04
% 2.61/1.39  Abstraction          : 0.01
% 2.61/1.39  MUC search           : 0.00
% 2.61/1.39  Cooper               : 0.00
% 2.61/1.39  Total                : 0.61
% 2.61/1.39  Index Insertion      : 0.00
% 2.61/1.39  Index Deletion       : 0.00
% 2.61/1.39  Index Matching       : 0.00
% 2.61/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
