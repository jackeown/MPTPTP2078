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
% DateTime   : Thu Dec  3 09:47:33 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   44 (  53 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  58 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_60,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_118,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_127,plain,(
    ! [A_59,C_60] :
      ( ~ r1_xboole_0(A_59,A_59)
      | ~ r2_hidden(C_60,A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_118])).

tff(c_131,plain,(
    ! [C_60] : ~ r2_hidden(C_60,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_127])).

tff(c_62,plain,(
    r1_tarski(k1_tarski('#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_142,plain,(
    ! [B_65,A_66] :
      ( k1_tarski(B_65) = A_66
      | k1_xboole_0 = A_66
      | ~ r1_tarski(A_66,k1_tarski(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_154,plain,
    ( k1_tarski('#skF_7') = k1_tarski('#skF_6')
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_142])).

tff(c_157,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_36,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_175,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_36])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_175])).

tff(c_185,plain,(
    k1_tarski('#skF_7') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_204,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_36])).

tff(c_34,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_224,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_204,c_34])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:40:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.22  
% 2.01/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.01/1.22  
% 2.01/1.22  %Foreground sorts:
% 2.01/1.22  
% 2.01/1.22  
% 2.01/1.22  %Background operators:
% 2.01/1.22  
% 2.01/1.22  
% 2.01/1.22  %Foreground operators:
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.22  tff('#skF_7', type, '#skF_7': $i).
% 2.01/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.01/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.01/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.01/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.22  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.01/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.01/1.22  
% 2.12/1.23  tff(f_84, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.12/1.23  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.12/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.12/1.23  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.12/1.23  tff(f_79, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.12/1.23  tff(f_65, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.12/1.23  tff(c_60, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.23  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.23  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.23  tff(c_118, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.23  tff(c_127, plain, (![A_59, C_60]: (~r1_xboole_0(A_59, A_59) | ~r2_hidden(C_60, A_59))), inference(superposition, [status(thm), theory('equality')], [c_2, c_118])).
% 2.12/1.23  tff(c_131, plain, (![C_60]: (~r2_hidden(C_60, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_127])).
% 2.12/1.23  tff(c_62, plain, (r1_tarski(k1_tarski('#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.23  tff(c_142, plain, (![B_65, A_66]: (k1_tarski(B_65)=A_66 | k1_xboole_0=A_66 | ~r1_tarski(A_66, k1_tarski(B_65)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.23  tff(c_154, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_6') | k1_tarski('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_142])).
% 2.12/1.23  tff(c_157, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_154])).
% 2.12/1.23  tff(c_36, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.23  tff(c_175, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_157, c_36])).
% 2.12/1.23  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_175])).
% 2.12/1.23  tff(c_185, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_154])).
% 2.12/1.23  tff(c_204, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_36])).
% 2.12/1.23  tff(c_34, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.23  tff(c_224, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_204, c_34])).
% 2.12/1.23  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_224])).
% 2.12/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.23  
% 2.12/1.23  Inference rules
% 2.12/1.23  ----------------------
% 2.12/1.23  #Ref     : 0
% 2.12/1.23  #Sup     : 38
% 2.12/1.23  #Fact    : 0
% 2.12/1.23  #Define  : 0
% 2.12/1.23  #Split   : 1
% 2.12/1.23  #Chain   : 0
% 2.12/1.23  #Close   : 0
% 2.12/1.23  
% 2.12/1.23  Ordering : KBO
% 2.12/1.23  
% 2.12/1.23  Simplification rules
% 2.12/1.23  ----------------------
% 2.12/1.23  #Subsume      : 2
% 2.12/1.23  #Demod        : 16
% 2.12/1.23  #Tautology    : 24
% 2.12/1.23  #SimpNegUnit  : 2
% 2.12/1.23  #BackRed      : 2
% 2.12/1.23  
% 2.12/1.23  #Partial instantiations: 0
% 2.12/1.23  #Strategies tried      : 1
% 2.12/1.23  
% 2.12/1.23  Timing (in seconds)
% 2.12/1.23  ----------------------
% 2.12/1.23  Preprocessing        : 0.32
% 2.12/1.23  Parsing              : 0.16
% 2.12/1.23  CNF conversion       : 0.03
% 2.12/1.23  Main loop            : 0.16
% 2.12/1.23  Inferencing          : 0.05
% 2.12/1.24  Reduction            : 0.06
% 2.12/1.24  Demodulation         : 0.04
% 2.12/1.24  BG Simplification    : 0.02
% 2.12/1.24  Subsumption          : 0.03
% 2.12/1.24  Abstraction          : 0.01
% 2.12/1.24  MUC search           : 0.00
% 2.12/1.24  Cooper               : 0.00
% 2.12/1.24  Total                : 0.50
% 2.12/1.24  Index Insertion      : 0.00
% 2.12/1.24  Index Deletion       : 0.00
% 2.12/1.24  Index Matching       : 0.00
% 2.12/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
