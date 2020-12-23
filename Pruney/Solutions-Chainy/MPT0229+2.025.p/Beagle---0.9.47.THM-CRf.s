%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:56 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   49 (  94 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 ( 148 expanded)
%              Number of equality atoms :   34 (  93 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,(
    ! [D_39,A_40,B_41] :
      ( r2_hidden(D_39,A_40)
      | ~ r2_hidden(D_39,k4_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_311,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_67,B_68)),A_67)
      | k4_xboole_0(A_67,B_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_103])).

tff(c_109,plain,(
    ! [D_42,B_43,A_44] :
      ( ~ r2_hidden(D_42,B_43)
      | ~ r2_hidden(D_42,k4_xboole_0(A_44,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    ! [A_44,B_43] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_44,B_43)),B_43)
      | k4_xboole_0(A_44,B_43) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_109])).

tff(c_349,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_311,c_114])).

tff(c_54,plain,(
    r1_tarski(k1_tarski('#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_146,plain,(
    ! [B_50,A_51] :
      ( k1_tarski(B_50) = A_51
      | k1_xboole_0 = A_51
      | ~ r1_tarski(A_51,k1_tarski(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_158,plain,
    ( k1_tarski('#skF_7') = k1_tarski('#skF_6')
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_146])).

tff(c_161,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_48,plain,(
    ! [B_27] : k4_xboole_0(k1_tarski(B_27),k1_tarski(B_27)) != k1_tarski(B_27) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_182,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) != k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_48])).

tff(c_203,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_161,c_182])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_203])).

tff(c_360,plain,(
    k1_tarski('#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_52,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_359,plain,(
    k1_tarski('#skF_7') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_68,plain,(
    ! [C_33,A_34] :
      ( C_33 = A_34
      | ~ r2_hidden(C_33,k1_tarski(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [A_34] :
      ( '#skF_3'(k1_tarski(A_34)) = A_34
      | k1_tarski(A_34) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_387,plain,
    ( '#skF_3'(k1_tarski('#skF_6')) = '#skF_7'
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_76])).

tff(c_412,plain,
    ( '#skF_3'(k1_tarski('#skF_6')) = '#skF_7'
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_387])).

tff(c_413,plain,(
    '#skF_3'(k1_tarski('#skF_6')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_412])).

tff(c_423,plain,
    ( '#skF_7' = '#skF_6'
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_76])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_52,c_423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:24:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.33  
% 2.01/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.33  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 2.32/1.33  
% 2.32/1.33  %Foreground sorts:
% 2.32/1.33  
% 2.32/1.33  
% 2.32/1.33  %Background operators:
% 2.32/1.33  
% 2.32/1.33  
% 2.32/1.33  %Foreground operators:
% 2.32/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.32/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.32/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.32/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.32/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.32/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.32/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.33  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.32/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.32/1.33  
% 2.32/1.34  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.32/1.34  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.32/1.34  tff(f_74, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.32/1.34  tff(f_64, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.32/1.34  tff(f_69, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.32/1.34  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.32/1.34  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.32/1.34  tff(c_103, plain, (![D_39, A_40, B_41]: (r2_hidden(D_39, A_40) | ~r2_hidden(D_39, k4_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.34  tff(c_311, plain, (![A_67, B_68]: (r2_hidden('#skF_3'(k4_xboole_0(A_67, B_68)), A_67) | k4_xboole_0(A_67, B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_103])).
% 2.32/1.34  tff(c_109, plain, (![D_42, B_43, A_44]: (~r2_hidden(D_42, B_43) | ~r2_hidden(D_42, k4_xboole_0(A_44, B_43)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.34  tff(c_114, plain, (![A_44, B_43]: (~r2_hidden('#skF_3'(k4_xboole_0(A_44, B_43)), B_43) | k4_xboole_0(A_44, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_109])).
% 2.32/1.34  tff(c_349, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_311, c_114])).
% 2.32/1.34  tff(c_54, plain, (r1_tarski(k1_tarski('#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.34  tff(c_146, plain, (![B_50, A_51]: (k1_tarski(B_50)=A_51 | k1_xboole_0=A_51 | ~r1_tarski(A_51, k1_tarski(B_50)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.34  tff(c_158, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_6') | k1_tarski('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_146])).
% 2.32/1.34  tff(c_161, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_158])).
% 2.32/1.34  tff(c_48, plain, (![B_27]: (k4_xboole_0(k1_tarski(B_27), k1_tarski(B_27))!=k1_tarski(B_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.32/1.34  tff(c_182, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)!=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_161, c_48])).
% 2.32/1.34  tff(c_203, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_161, c_161, c_182])).
% 2.32/1.34  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_349, c_203])).
% 2.32/1.34  tff(c_360, plain, (k1_tarski('#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_158])).
% 2.32/1.34  tff(c_52, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.34  tff(c_359, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_158])).
% 2.32/1.34  tff(c_68, plain, (![C_33, A_34]: (C_33=A_34 | ~r2_hidden(C_33, k1_tarski(A_34)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.32/1.34  tff(c_76, plain, (![A_34]: ('#skF_3'(k1_tarski(A_34))=A_34 | k1_tarski(A_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_68])).
% 2.32/1.34  tff(c_387, plain, ('#skF_3'(k1_tarski('#skF_6'))='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_359, c_76])).
% 2.32/1.34  tff(c_412, plain, ('#skF_3'(k1_tarski('#skF_6'))='#skF_7' | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_359, c_387])).
% 2.32/1.34  tff(c_413, plain, ('#skF_3'(k1_tarski('#skF_6'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_360, c_412])).
% 2.32/1.34  tff(c_423, plain, ('#skF_7'='#skF_6' | k1_tarski('#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_413, c_76])).
% 2.32/1.34  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_360, c_52, c_423])).
% 2.32/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.34  
% 2.32/1.34  Inference rules
% 2.32/1.34  ----------------------
% 2.32/1.34  #Ref     : 0
% 2.32/1.34  #Sup     : 89
% 2.32/1.34  #Fact    : 0
% 2.32/1.34  #Define  : 0
% 2.32/1.34  #Split   : 1
% 2.32/1.34  #Chain   : 0
% 2.32/1.34  #Close   : 0
% 2.32/1.34  
% 2.32/1.34  Ordering : KBO
% 2.32/1.34  
% 2.32/1.34  Simplification rules
% 2.32/1.34  ----------------------
% 2.32/1.34  #Subsume      : 10
% 2.32/1.34  #Demod        : 30
% 2.32/1.34  #Tautology    : 46
% 2.32/1.34  #SimpNegUnit  : 4
% 2.32/1.34  #BackRed      : 4
% 2.32/1.34  
% 2.32/1.34  #Partial instantiations: 0
% 2.32/1.34  #Strategies tried      : 1
% 2.32/1.34  
% 2.32/1.34  Timing (in seconds)
% 2.32/1.34  ----------------------
% 2.32/1.35  Preprocessing        : 0.33
% 2.32/1.35  Parsing              : 0.17
% 2.32/1.35  CNF conversion       : 0.02
% 2.32/1.35  Main loop            : 0.22
% 2.32/1.35  Inferencing          : 0.08
% 2.32/1.35  Reduction            : 0.07
% 2.32/1.35  Demodulation         : 0.05
% 2.32/1.35  BG Simplification    : 0.02
% 2.32/1.35  Subsumption          : 0.04
% 2.32/1.35  Abstraction          : 0.01
% 2.32/1.35  MUC search           : 0.00
% 2.32/1.35  Cooper               : 0.00
% 2.32/1.35  Total                : 0.58
% 2.32/1.35  Index Insertion      : 0.00
% 2.32/1.35  Index Deletion       : 0.00
% 2.32/1.35  Index Matching       : 0.00
% 2.32/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
