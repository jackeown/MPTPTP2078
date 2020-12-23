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
% DateTime   : Thu Dec  3 09:47:51 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_68,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_70,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_141,plain,(
    ! [B_54,A_55] : k2_xboole_0(B_54,A_55) = k2_xboole_0(A_55,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_180,plain,(
    ! [A_56,B_57] : r1_tarski(A_56,k2_xboole_0(B_57,A_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_44])).

tff(c_189,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_180])).

tff(c_50,plain,(
    ! [C_32] : r2_hidden(C_32,k1_tarski(C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_804,plain,(
    ! [C_97,B_98,A_99] :
      ( r2_hidden(C_97,B_98)
      | ~ r2_hidden(C_97,A_99)
      | ~ r1_tarski(A_99,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_811,plain,(
    ! [C_100,B_101] :
      ( r2_hidden(C_100,B_101)
      | ~ r1_tarski(k1_tarski(C_100),B_101) ) ),
    inference(resolution,[status(thm)],[c_50,c_804])).

tff(c_827,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_189,c_811])).

tff(c_48,plain,(
    ! [C_32,A_28] :
      ( C_32 = A_28
      | ~ r2_hidden(C_32,k1_tarski(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_836,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_827,c_48])).

tff(c_841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_836])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.47/1.35  
% 2.47/1.35  %Foreground sorts:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Background operators:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Foreground operators:
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.47/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.47/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.35  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.47/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.47/1.35  
% 2.47/1.36  tff(f_86, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.47/1.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.47/1.36  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.47/1.36  tff(f_73, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.47/1.36  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.47/1.36  tff(c_68, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.47/1.36  tff(c_70, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.47/1.36  tff(c_141, plain, (![B_54, A_55]: (k2_xboole_0(B_54, A_55)=k2_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.36  tff(c_44, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.36  tff(c_180, plain, (![A_56, B_57]: (r1_tarski(A_56, k2_xboole_0(B_57, A_56)))), inference(superposition, [status(thm), theory('equality')], [c_141, c_44])).
% 2.47/1.36  tff(c_189, plain, (r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_180])).
% 2.47/1.36  tff(c_50, plain, (![C_32]: (r2_hidden(C_32, k1_tarski(C_32)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.47/1.36  tff(c_804, plain, (![C_97, B_98, A_99]: (r2_hidden(C_97, B_98) | ~r2_hidden(C_97, A_99) | ~r1_tarski(A_99, B_98))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.47/1.36  tff(c_811, plain, (![C_100, B_101]: (r2_hidden(C_100, B_101) | ~r1_tarski(k1_tarski(C_100), B_101))), inference(resolution, [status(thm)], [c_50, c_804])).
% 2.47/1.36  tff(c_827, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_189, c_811])).
% 2.47/1.36  tff(c_48, plain, (![C_32, A_28]: (C_32=A_28 | ~r2_hidden(C_32, k1_tarski(A_28)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.47/1.36  tff(c_836, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_827, c_48])).
% 2.47/1.36  tff(c_841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_836])).
% 2.47/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  Inference rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Ref     : 0
% 2.47/1.36  #Sup     : 182
% 2.47/1.36  #Fact    : 0
% 2.47/1.36  #Define  : 0
% 2.47/1.36  #Split   : 1
% 2.47/1.36  #Chain   : 0
% 2.47/1.36  #Close   : 0
% 2.47/1.36  
% 2.47/1.36  Ordering : KBO
% 2.47/1.36  
% 2.47/1.36  Simplification rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Subsume      : 2
% 2.47/1.36  #Demod        : 68
% 2.47/1.36  #Tautology    : 139
% 2.47/1.36  #SimpNegUnit  : 1
% 2.47/1.36  #BackRed      : 0
% 2.47/1.36  
% 2.47/1.36  #Partial instantiations: 0
% 2.47/1.36  #Strategies tried      : 1
% 2.47/1.36  
% 2.47/1.36  Timing (in seconds)
% 2.47/1.36  ----------------------
% 2.47/1.36  Preprocessing        : 0.33
% 2.47/1.36  Parsing              : 0.17
% 2.47/1.36  CNF conversion       : 0.02
% 2.47/1.36  Main loop            : 0.28
% 2.47/1.36  Inferencing          : 0.10
% 2.47/1.36  Reduction            : 0.10
% 2.47/1.36  Demodulation         : 0.08
% 2.47/1.36  BG Simplification    : 0.02
% 2.47/1.36  Subsumption          : 0.05
% 2.47/1.36  Abstraction          : 0.01
% 2.47/1.36  MUC search           : 0.00
% 2.47/1.36  Cooper               : 0.00
% 2.47/1.36  Total                : 0.64
% 2.47/1.36  Index Insertion      : 0.00
% 2.47/1.36  Index Deletion       : 0.00
% 2.47/1.36  Index Matching       : 0.00
% 2.47/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
