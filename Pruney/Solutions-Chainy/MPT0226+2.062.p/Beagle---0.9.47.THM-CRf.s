%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:45 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  55 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [A_33,B_34] :
      ( ~ r2_hidden(A_33,B_34)
      | ~ r1_xboole_0(k1_tarski(A_33),B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_87,plain,(
    ! [A_33] : ~ r2_hidden(A_33,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_48,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(k1_tarski(A_22),B_23)
      | r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_94,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = A_38
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_154,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(k1_tarski(A_50),B_51) = k1_tarski(A_50)
      | r2_hidden(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_46,c_94])).

tff(c_50,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_164,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_50])).

tff(c_181,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_185,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_181,c_10])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_185])).

tff(c_190,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_12,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_208,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_12])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.29  
% 1.97/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.29  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 1.97/1.29  
% 1.97/1.29  %Foreground sorts:
% 1.97/1.29  
% 1.97/1.29  
% 1.97/1.29  %Background operators:
% 1.97/1.29  
% 1.97/1.29  
% 1.97/1.29  %Foreground operators:
% 1.97/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.97/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.97/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.29  tff('#skF_6', type, '#skF_6': $i).
% 1.97/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.97/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.97/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.29  
% 1.97/1.30  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.97/1.30  tff(f_58, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.97/1.30  tff(f_68, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.97/1.30  tff(f_63, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.97/1.30  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.97/1.30  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.97/1.30  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.30  tff(c_82, plain, (![A_33, B_34]: (~r2_hidden(A_33, B_34) | ~r1_xboole_0(k1_tarski(A_33), B_34))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.97/1.30  tff(c_87, plain, (![A_33]: (~r2_hidden(A_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_82])).
% 1.97/1.30  tff(c_48, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.30  tff(c_46, plain, (![A_22, B_23]: (r1_xboole_0(k1_tarski(A_22), B_23) | r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.97/1.30  tff(c_94, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=A_38 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.30  tff(c_154, plain, (![A_50, B_51]: (k4_xboole_0(k1_tarski(A_50), B_51)=k1_tarski(A_50) | r2_hidden(A_50, B_51))), inference(resolution, [status(thm)], [c_46, c_94])).
% 1.97/1.30  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.30  tff(c_164, plain, (k1_tarski('#skF_5')=k1_xboole_0 | r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_50])).
% 1.97/1.30  tff(c_181, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_164])).
% 1.97/1.30  tff(c_10, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.97/1.30  tff(c_185, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_181, c_10])).
% 1.97/1.30  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_185])).
% 1.97/1.30  tff(c_190, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_164])).
% 1.97/1.30  tff(c_12, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.97/1.30  tff(c_208, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_190, c_12])).
% 1.97/1.30  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_208])).
% 1.97/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.30  
% 1.97/1.30  Inference rules
% 1.97/1.30  ----------------------
% 1.97/1.30  #Ref     : 0
% 1.97/1.30  #Sup     : 36
% 1.97/1.30  #Fact    : 0
% 1.97/1.30  #Define  : 0
% 1.97/1.30  #Split   : 2
% 1.97/1.30  #Chain   : 0
% 1.97/1.30  #Close   : 0
% 1.97/1.30  
% 1.97/1.30  Ordering : KBO
% 1.97/1.30  
% 1.97/1.30  Simplification rules
% 1.97/1.30  ----------------------
% 1.97/1.30  #Subsume      : 2
% 1.97/1.30  #Demod        : 4
% 1.97/1.30  #Tautology    : 22
% 1.97/1.30  #SimpNegUnit  : 4
% 1.97/1.30  #BackRed      : 1
% 1.97/1.30  
% 1.97/1.30  #Partial instantiations: 0
% 1.97/1.30  #Strategies tried      : 1
% 1.97/1.30  
% 1.97/1.30  Timing (in seconds)
% 1.97/1.30  ----------------------
% 1.97/1.30  Preprocessing        : 0.34
% 1.97/1.30  Parsing              : 0.17
% 1.97/1.30  CNF conversion       : 0.02
% 1.97/1.30  Main loop            : 0.16
% 1.97/1.30  Inferencing          : 0.05
% 1.97/1.30  Reduction            : 0.05
% 1.97/1.30  Demodulation         : 0.04
% 1.97/1.30  BG Simplification    : 0.01
% 1.97/1.30  Subsumption          : 0.03
% 1.97/1.30  Abstraction          : 0.01
% 1.97/1.30  MUC search           : 0.00
% 1.97/1.30  Cooper               : 0.00
% 1.97/1.30  Total                : 0.52
% 1.97/1.30  Index Insertion      : 0.00
% 1.97/1.31  Index Deletion       : 0.00
% 1.97/1.31  Index Matching       : 0.00
% 1.97/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
