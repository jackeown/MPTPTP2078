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
% DateTime   : Thu Dec  3 09:47:51 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   40 (  42 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  32 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_68,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_70,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_145,plain,(
    ! [B_54,A_55] : k2_xboole_0(B_54,A_55) = k2_xboole_0(A_55,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_350,plain,(
    ! [A_64,B_65] : r1_tarski(A_64,k2_xboole_0(B_65,A_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_44])).

tff(c_365,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_350])).

tff(c_50,plain,(
    ! [C_32] : r2_hidden(C_32,k1_tarski(C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1045,plain,(
    ! [C_109,B_110,A_111] :
      ( r2_hidden(C_109,B_110)
      | ~ r2_hidden(C_109,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1168,plain,(
    ! [C_118,B_119] :
      ( r2_hidden(C_118,B_119)
      | ~ r1_tarski(k1_tarski(C_118),B_119) ) ),
    inference(resolution,[status(thm)],[c_50,c_1045])).

tff(c_1184,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_365,c_1168])).

tff(c_48,plain,(
    ! [C_32,A_28] :
      ( C_32 = A_28
      | ~ r2_hidden(C_32,k1_tarski(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1193,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1184,c_48])).

tff(c_1198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:45:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.43  
% 2.81/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.43  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.81/1.43  
% 2.81/1.43  %Foreground sorts:
% 2.81/1.43  
% 2.81/1.43  
% 2.81/1.43  %Background operators:
% 2.81/1.43  
% 2.81/1.43  
% 2.81/1.43  %Foreground operators:
% 2.81/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.81/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.81/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.81/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.81/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.81/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.81/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.81/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.81/1.43  
% 2.81/1.44  tff(f_86, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.81/1.44  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.81/1.44  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.81/1.44  tff(f_73, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.81/1.44  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.81/1.44  tff(c_68, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.44  tff(c_70, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.44  tff(c_145, plain, (![B_54, A_55]: (k2_xboole_0(B_54, A_55)=k2_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.44  tff(c_44, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.44  tff(c_350, plain, (![A_64, B_65]: (r1_tarski(A_64, k2_xboole_0(B_65, A_64)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_44])).
% 2.81/1.44  tff(c_365, plain, (r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_350])).
% 2.81/1.44  tff(c_50, plain, (![C_32]: (r2_hidden(C_32, k1_tarski(C_32)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.44  tff(c_1045, plain, (![C_109, B_110, A_111]: (r2_hidden(C_109, B_110) | ~r2_hidden(C_109, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.81/1.44  tff(c_1168, plain, (![C_118, B_119]: (r2_hidden(C_118, B_119) | ~r1_tarski(k1_tarski(C_118), B_119))), inference(resolution, [status(thm)], [c_50, c_1045])).
% 2.81/1.44  tff(c_1184, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_365, c_1168])).
% 2.81/1.44  tff(c_48, plain, (![C_32, A_28]: (C_32=A_28 | ~r2_hidden(C_32, k1_tarski(A_28)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.44  tff(c_1193, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_1184, c_48])).
% 2.81/1.44  tff(c_1198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1193])).
% 2.81/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.44  
% 2.81/1.44  Inference rules
% 2.81/1.44  ----------------------
% 2.81/1.44  #Ref     : 0
% 2.81/1.44  #Sup     : 281
% 2.81/1.44  #Fact    : 0
% 2.81/1.44  #Define  : 0
% 2.81/1.44  #Split   : 1
% 2.81/1.44  #Chain   : 0
% 2.81/1.44  #Close   : 0
% 2.81/1.44  
% 2.81/1.44  Ordering : KBO
% 2.81/1.44  
% 2.81/1.44  Simplification rules
% 2.81/1.44  ----------------------
% 2.81/1.44  #Subsume      : 34
% 2.81/1.44  #Demod        : 120
% 2.81/1.44  #Tautology    : 195
% 2.81/1.44  #SimpNegUnit  : 2
% 2.81/1.44  #BackRed      : 5
% 2.81/1.44  
% 2.81/1.44  #Partial instantiations: 0
% 2.81/1.44  #Strategies tried      : 1
% 2.81/1.44  
% 2.81/1.44  Timing (in seconds)
% 2.81/1.44  ----------------------
% 2.81/1.44  Preprocessing        : 0.33
% 2.81/1.44  Parsing              : 0.16
% 2.81/1.44  CNF conversion       : 0.03
% 2.81/1.44  Main loop            : 0.36
% 2.81/1.44  Inferencing          : 0.13
% 2.81/1.44  Reduction            : 0.13
% 2.81/1.44  Demodulation         : 0.10
% 2.81/1.44  BG Simplification    : 0.02
% 2.81/1.44  Subsumption          : 0.06
% 2.81/1.44  Abstraction          : 0.02
% 2.81/1.44  MUC search           : 0.00
% 2.81/1.44  Cooper               : 0.00
% 2.81/1.44  Total                : 0.71
% 2.81/1.44  Index Insertion      : 0.00
% 2.81/1.44  Index Deletion       : 0.00
% 2.81/1.44  Index Matching       : 0.00
% 2.81/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
