%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:17 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   47 (  54 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  57 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_32,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_33,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_54,plain,(
    '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_56,plain,(
    r1_tarski(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_172,plain,(
    ! [B_53,A_54] :
      ( k1_tarski(B_53) = A_54
      | k1_xboole_0 = A_54
      | ~ r1_tarski(A_54,k1_tarski(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_182,plain,
    ( k2_tarski('#skF_6','#skF_7') = k1_tarski('#skF_8')
    | k2_tarski('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_172])).

tff(c_187,plain,(
    k2_tarski('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_71,plain,(
    ! [D_34,B_35] : r2_hidden(D_34,k2_tarski(D_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [D_34,B_35] : ~ v1_xboole_0(k2_tarski(D_34,B_35)) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_198,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_75])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_198])).

tff(c_207,plain,(
    k2_tarski('#skF_6','#skF_7') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_26,plain,(
    ! [D_15,B_11] : r2_hidden(D_15,k2_tarski(D_15,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_223,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_26])).

tff(c_10,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_238,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_223,c_10])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.22  
% 1.85/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.22  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2
% 1.85/1.22  
% 1.85/1.22  %Foreground sorts:
% 1.85/1.22  
% 1.85/1.22  
% 1.85/1.22  %Background operators:
% 1.85/1.22  
% 1.85/1.22  
% 1.85/1.22  %Foreground operators:
% 1.85/1.22  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.85/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.85/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.85/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.85/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.85/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.85/1.22  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.85/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.22  tff('#skF_8', type, '#skF_8': $i).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.85/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.85/1.22  
% 2.06/1.23  tff(f_68, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.06/1.23  tff(f_32, axiom, (k1_xboole_0 = o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_xboole_0)).
% 2.06/1.23  tff(f_33, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 2.06/1.23  tff(f_63, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.06/1.23  tff(f_49, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.06/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.06/1.23  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.06/1.23  tff(c_54, plain, ('#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.06/1.23  tff(c_6, plain, (o_0_0_xboole_0=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.23  tff(c_8, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.23  tff(c_57, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.06/1.23  tff(c_56, plain, (r1_tarski(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.06/1.23  tff(c_172, plain, (![B_53, A_54]: (k1_tarski(B_53)=A_54 | k1_xboole_0=A_54 | ~r1_tarski(A_54, k1_tarski(B_53)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.06/1.23  tff(c_182, plain, (k2_tarski('#skF_6', '#skF_7')=k1_tarski('#skF_8') | k2_tarski('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_172])).
% 2.06/1.23  tff(c_187, plain, (k2_tarski('#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_182])).
% 2.06/1.23  tff(c_71, plain, (![D_34, B_35]: (r2_hidden(D_34, k2_tarski(D_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.23  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.23  tff(c_75, plain, (![D_34, B_35]: (~v1_xboole_0(k2_tarski(D_34, B_35)))), inference(resolution, [status(thm)], [c_71, c_2])).
% 2.06/1.23  tff(c_198, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_187, c_75])).
% 2.06/1.23  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_198])).
% 2.06/1.23  tff(c_207, plain, (k2_tarski('#skF_6', '#skF_7')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_182])).
% 2.06/1.23  tff(c_26, plain, (![D_15, B_11]: (r2_hidden(D_15, k2_tarski(D_15, B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.23  tff(c_223, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_26])).
% 2.06/1.23  tff(c_10, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.06/1.23  tff(c_238, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_223, c_10])).
% 2.06/1.23  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_238])).
% 2.06/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  Inference rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Ref     : 0
% 2.06/1.23  #Sup     : 43
% 2.06/1.23  #Fact    : 0
% 2.06/1.23  #Define  : 0
% 2.06/1.23  #Split   : 1
% 2.06/1.23  #Chain   : 0
% 2.06/1.23  #Close   : 0
% 2.06/1.23  
% 2.06/1.23  Ordering : KBO
% 2.06/1.23  
% 2.06/1.23  Simplification rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Subsume      : 4
% 2.06/1.23  #Demod        : 10
% 2.06/1.23  #Tautology    : 26
% 2.06/1.23  #SimpNegUnit  : 4
% 2.06/1.23  #BackRed      : 3
% 2.06/1.23  
% 2.06/1.23  #Partial instantiations: 0
% 2.06/1.23  #Strategies tried      : 1
% 2.06/1.23  
% 2.06/1.23  Timing (in seconds)
% 2.06/1.23  ----------------------
% 2.06/1.23  Preprocessing        : 0.31
% 2.06/1.23  Parsing              : 0.15
% 2.06/1.23  CNF conversion       : 0.02
% 2.06/1.23  Main loop            : 0.17
% 2.06/1.23  Inferencing          : 0.05
% 2.06/1.23  Reduction            : 0.06
% 2.06/1.23  Demodulation         : 0.04
% 2.06/1.23  BG Simplification    : 0.02
% 2.06/1.23  Subsumption          : 0.03
% 2.06/1.23  Abstraction          : 0.01
% 2.06/1.23  MUC search           : 0.00
% 2.06/1.23  Cooper               : 0.00
% 2.06/1.23  Total                : 0.50
% 2.06/1.23  Index Insertion      : 0.00
% 2.06/1.24  Index Deletion       : 0.00
% 2.06/1.24  Index Matching       : 0.00
% 2.06/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
