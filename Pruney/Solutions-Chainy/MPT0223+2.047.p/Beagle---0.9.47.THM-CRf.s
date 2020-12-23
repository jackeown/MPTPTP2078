%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:22 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 106 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   55 ( 189 expanded)
%              Number of equality atoms :   25 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_64,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_48,plain,(
    ! [C_27] : r2_hidden(C_27,k1_tarski(C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_270,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,B_80)
      | ~ r2_hidden(C_81,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_361,plain,(
    ! [C_88,B_89,A_90] :
      ( ~ r2_hidden(C_88,B_89)
      | ~ r2_hidden(C_88,A_90)
      | k3_xboole_0(A_90,B_89) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_270])).

tff(c_386,plain,(
    ! [C_91,A_92] :
      ( ~ r2_hidden(C_91,A_92)
      | k3_xboole_0(A_92,k1_tarski(C_91)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_361])).

tff(c_393,plain,(
    ! [C_91] :
      ( ~ r2_hidden(C_91,k1_tarski(C_91))
      | k1_tarski(C_91) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_386])).

tff(c_395,plain,(
    ! [C_91] : k1_tarski(C_91) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_393])).

tff(c_148,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),B_63)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [C_27,A_23] :
      ( C_27 = A_23
      | ~ r2_hidden(C_27,k1_tarski(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_289,plain,(
    ! [A_84,A_85] :
      ( '#skF_1'(A_84,k1_tarski(A_85)) = A_85
      | r1_xboole_0(A_84,k1_tarski(A_85)) ) ),
    inference(resolution,[status(thm)],[c_148,c_46])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_491,plain,(
    ! [A_124,A_125] :
      ( k3_xboole_0(A_124,k1_tarski(A_125)) = k1_xboole_0
      | '#skF_1'(A_124,k1_tarski(A_125)) = A_125 ) ),
    inference(resolution,[status(thm)],[c_289,c_2])).

tff(c_66,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_506,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | '#skF_1'(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_66])).

tff(c_523,plain,(
    '#skF_1'(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_506])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_531,plain,
    ( r2_hidden('#skF_7',k1_tarski('#skF_6'))
    | r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_12])).

tff(c_607,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_531])).

tff(c_617,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_607,c_2])).

tff(c_619,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_66])).

tff(c_621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_619])).

tff(c_622,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_630,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_622,c_46])).

tff(c_636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_630])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:57:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.48  
% 2.72/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.48  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.72/1.48  
% 2.72/1.48  %Foreground sorts:
% 2.72/1.48  
% 2.72/1.48  
% 2.72/1.48  %Background operators:
% 2.72/1.48  
% 2.72/1.48  
% 2.72/1.48  %Foreground operators:
% 2.72/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.48  tff('#skF_7', type, '#skF_7': $i).
% 2.72/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.72/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.72/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.72/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.72/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.72/1.48  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.72/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.72/1.48  
% 2.87/1.49  tff(f_90, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.87/1.49  tff(f_79, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.87/1.49  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.87/1.49  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.87/1.49  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.87/1.49  tff(c_64, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.87/1.49  tff(c_48, plain, (![C_27]: (r2_hidden(C_27, k1_tarski(C_27)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.87/1.49  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.49  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.49  tff(c_270, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, B_80) | ~r2_hidden(C_81, A_79))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.87/1.49  tff(c_361, plain, (![C_88, B_89, A_90]: (~r2_hidden(C_88, B_89) | ~r2_hidden(C_88, A_90) | k3_xboole_0(A_90, B_89)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_270])).
% 2.87/1.49  tff(c_386, plain, (![C_91, A_92]: (~r2_hidden(C_91, A_92) | k3_xboole_0(A_92, k1_tarski(C_91))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_361])).
% 2.87/1.49  tff(c_393, plain, (![C_91]: (~r2_hidden(C_91, k1_tarski(C_91)) | k1_tarski(C_91)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_386])).
% 2.87/1.49  tff(c_395, plain, (![C_91]: (k1_tarski(C_91)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_393])).
% 2.87/1.49  tff(c_148, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), B_63) | r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.87/1.49  tff(c_46, plain, (![C_27, A_23]: (C_27=A_23 | ~r2_hidden(C_27, k1_tarski(A_23)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.87/1.49  tff(c_289, plain, (![A_84, A_85]: ('#skF_1'(A_84, k1_tarski(A_85))=A_85 | r1_xboole_0(A_84, k1_tarski(A_85)))), inference(resolution, [status(thm)], [c_148, c_46])).
% 2.87/1.49  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.49  tff(c_491, plain, (![A_124, A_125]: (k3_xboole_0(A_124, k1_tarski(A_125))=k1_xboole_0 | '#skF_1'(A_124, k1_tarski(A_125))=A_125)), inference(resolution, [status(thm)], [c_289, c_2])).
% 2.87/1.49  tff(c_66, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.87/1.49  tff(c_506, plain, (k1_tarski('#skF_6')=k1_xboole_0 | '#skF_1'(k1_tarski('#skF_6'), k1_tarski('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_491, c_66])).
% 2.87/1.49  tff(c_523, plain, ('#skF_1'(k1_tarski('#skF_6'), k1_tarski('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_395, c_506])).
% 2.87/1.49  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.87/1.49  tff(c_531, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6')) | r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_523, c_12])).
% 2.87/1.49  tff(c_607, plain, (r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_531])).
% 2.87/1.49  tff(c_617, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_607, c_2])).
% 2.87/1.49  tff(c_619, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_617, c_66])).
% 2.87/1.49  tff(c_621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_395, c_619])).
% 2.87/1.49  tff(c_622, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_531])).
% 2.87/1.49  tff(c_630, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_622, c_46])).
% 2.87/1.49  tff(c_636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_630])).
% 2.87/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.49  
% 2.87/1.49  Inference rules
% 2.87/1.49  ----------------------
% 2.87/1.49  #Ref     : 0
% 2.87/1.49  #Sup     : 137
% 2.87/1.49  #Fact    : 0
% 2.87/1.49  #Define  : 0
% 2.87/1.49  #Split   : 2
% 2.87/1.49  #Chain   : 0
% 2.87/1.49  #Close   : 0
% 2.87/1.49  
% 2.87/1.49  Ordering : KBO
% 2.87/1.49  
% 2.87/1.49  Simplification rules
% 2.87/1.49  ----------------------
% 2.87/1.49  #Subsume      : 17
% 2.87/1.49  #Demod        : 48
% 2.87/1.49  #Tautology    : 61
% 2.87/1.49  #SimpNegUnit  : 8
% 2.87/1.49  #BackRed      : 1
% 2.87/1.49  
% 2.87/1.49  #Partial instantiations: 0
% 2.87/1.49  #Strategies tried      : 1
% 2.87/1.49  
% 2.87/1.49  Timing (in seconds)
% 2.87/1.49  ----------------------
% 2.87/1.50  Preprocessing        : 0.36
% 2.87/1.50  Parsing              : 0.19
% 2.87/1.50  CNF conversion       : 0.03
% 2.87/1.50  Main loop            : 0.31
% 2.87/1.50  Inferencing          : 0.11
% 2.87/1.50  Reduction            : 0.10
% 2.87/1.50  Demodulation         : 0.07
% 2.87/1.50  BG Simplification    : 0.02
% 2.87/1.50  Subsumption          : 0.06
% 2.87/1.50  Abstraction          : 0.02
% 2.87/1.50  MUC search           : 0.00
% 2.87/1.50  Cooper               : 0.00
% 2.87/1.50  Total                : 0.71
% 2.87/1.50  Index Insertion      : 0.00
% 2.87/1.50  Index Deletion       : 0.00
% 2.87/1.50  Index Matching       : 0.00
% 2.87/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
