%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:33 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_60,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r1_xboole_0(A_53,B_54)
      | ~ r2_hidden(C_55,k3_xboole_0(A_53,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_119,plain,(
    ! [A_6,C_55] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_55,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_116])).

tff(c_121,plain,(
    ! [C_55] : ~ r2_hidden(C_55,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_119])).

tff(c_62,plain,(
    r1_tarski(k1_tarski('#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_137,plain,(
    ! [B_62,A_63] :
      ( k1_tarski(B_62) = A_63
      | k1_xboole_0 = A_63
      | ~ r1_tarski(A_63,k1_tarski(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_149,plain,
    ( k1_tarski('#skF_7') = k1_tarski('#skF_6')
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_137])).

tff(c_152,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_36,plain,(
    ! [C_19] : r2_hidden(C_19,k1_tarski(C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_170,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_36])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_170])).

tff(c_180,plain,(
    k1_tarski('#skF_7') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_199,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_36])).

tff(c_34,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_211,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_199,c_34])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 1.99/1.23  
% 1.99/1.23  %Foreground sorts:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Background operators:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Foreground operators:
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.23  tff('#skF_7', type, '#skF_7': $i).
% 1.99/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.99/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.99/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.23  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.99/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.99/1.23  
% 1.99/1.23  tff(f_84, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.99/1.23  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.99/1.23  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.99/1.23  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.99/1.23  tff(f_79, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.99/1.23  tff(f_65, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.99/1.23  tff(c_60, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.99/1.23  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.23  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.23  tff(c_116, plain, (![A_53, B_54, C_55]: (~r1_xboole_0(A_53, B_54) | ~r2_hidden(C_55, k3_xboole_0(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.23  tff(c_119, plain, (![A_6, C_55]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_116])).
% 1.99/1.23  tff(c_121, plain, (![C_55]: (~r2_hidden(C_55, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_119])).
% 1.99/1.23  tff(c_62, plain, (r1_tarski(k1_tarski('#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.99/1.23  tff(c_137, plain, (![B_62, A_63]: (k1_tarski(B_62)=A_63 | k1_xboole_0=A_63 | ~r1_tarski(A_63, k1_tarski(B_62)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.99/1.23  tff(c_149, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_6') | k1_tarski('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_137])).
% 1.99/1.23  tff(c_152, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_149])).
% 1.99/1.23  tff(c_36, plain, (![C_19]: (r2_hidden(C_19, k1_tarski(C_19)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.23  tff(c_170, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_36])).
% 1.99/1.23  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_170])).
% 1.99/1.23  tff(c_180, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_149])).
% 1.99/1.23  tff(c_199, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_180, c_36])).
% 1.99/1.23  tff(c_34, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.23  tff(c_211, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_199, c_34])).
% 1.99/1.23  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_211])).
% 1.99/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  Inference rules
% 1.99/1.23  ----------------------
% 1.99/1.23  #Ref     : 0
% 1.99/1.23  #Sup     : 35
% 1.99/1.23  #Fact    : 0
% 1.99/1.23  #Define  : 0
% 1.99/1.23  #Split   : 1
% 1.99/1.23  #Chain   : 0
% 1.99/1.23  #Close   : 0
% 1.99/1.23  
% 1.99/1.23  Ordering : KBO
% 1.99/1.23  
% 1.99/1.23  Simplification rules
% 1.99/1.23  ----------------------
% 1.99/1.23  #Subsume      : 2
% 1.99/1.23  #Demod        : 17
% 1.99/1.23  #Tautology    : 23
% 1.99/1.23  #SimpNegUnit  : 2
% 1.99/1.23  #BackRed      : 2
% 1.99/1.23  
% 1.99/1.24  #Partial instantiations: 0
% 1.99/1.24  #Strategies tried      : 1
% 1.99/1.24  
% 1.99/1.24  Timing (in seconds)
% 1.99/1.24  ----------------------
% 1.99/1.24  Preprocessing        : 0.32
% 1.99/1.24  Parsing              : 0.17
% 1.99/1.24  CNF conversion       : 0.03
% 1.99/1.24  Main loop            : 0.16
% 1.99/1.24  Inferencing          : 0.04
% 1.99/1.24  Reduction            : 0.06
% 1.99/1.24  Demodulation         : 0.04
% 1.99/1.24  BG Simplification    : 0.01
% 1.99/1.24  Subsumption          : 0.03
% 1.99/1.24  Abstraction          : 0.01
% 1.99/1.24  MUC search           : 0.00
% 1.99/1.24  Cooper               : 0.00
% 1.99/1.24  Total                : 0.50
% 1.99/1.24  Index Insertion      : 0.00
% 1.99/1.24  Index Deletion       : 0.00
% 1.99/1.24  Index Matching       : 0.00
% 1.99/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
