%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:54 EST 2020

% Result     : Theorem 11.02s
% Output     : CNFRefutation 11.02s
% Verified   : 
% Statistics : Number of formulae       :   44 (  46 expanded)
%              Number of leaves         :   31 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  42 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_1 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_118,plain,(
    '#skF_11' != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_100,plain,(
    ! [C_45] : r2_hidden(C_45,k1_tarski(C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_120,plain,(
    k2_xboole_0(k1_tarski('#skF_10'),k1_tarski('#skF_11')) = k1_tarski('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    ! [D_19,A_14,B_15] :
      ( r2_hidden(D_19,k4_xboole_0(A_14,B_15))
      | r2_hidden(D_19,B_15)
      | ~ r2_hidden(D_19,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    ! [A_32,B_33] : k5_xboole_0(A_32,k4_xboole_0(B_33,A_32)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1425,plain,(
    ! [A_2769,B_2770,C_2771] :
      ( r2_hidden(A_2769,B_2770)
      | ~ r2_hidden(A_2769,C_2771)
      | r2_hidden(A_2769,k5_xboole_0(B_2770,C_2771)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_29448,plain,(
    ! [A_17593,A_17594,B_17595] :
      ( r2_hidden(A_17593,A_17594)
      | ~ r2_hidden(A_17593,k4_xboole_0(B_17595,A_17594))
      | r2_hidden(A_17593,k2_xboole_0(A_17594,B_17595)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1425])).

tff(c_34950,plain,(
    ! [D_19449,B_19450,A_19451] :
      ( r2_hidden(D_19449,k2_xboole_0(B_19450,A_19451))
      | r2_hidden(D_19449,B_19450)
      | ~ r2_hidden(D_19449,A_19451) ) ),
    inference(resolution,[status(thm)],[c_28,c_29448])).

tff(c_35499,plain,(
    ! [D_19709] :
      ( r2_hidden(D_19709,k1_tarski('#skF_10'))
      | r2_hidden(D_19709,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_19709,k1_tarski('#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_34950])).

tff(c_35695,plain,(
    r2_hidden('#skF_11',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_100,c_35499])).

tff(c_98,plain,(
    ! [C_45,A_41] :
      ( C_45 = A_41
      | ~ r2_hidden(C_45,k1_tarski(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_35702,plain,(
    '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_35695,c_98])).

tff(c_35752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_35702])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:44:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.02/4.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.02/4.21  
% 11.02/4.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.02/4.21  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_1 > #skF_9
% 11.02/4.21  
% 11.02/4.21  %Foreground sorts:
% 11.02/4.21  
% 11.02/4.21  
% 11.02/4.21  %Background operators:
% 11.02/4.21  
% 11.02/4.21  
% 11.02/4.21  %Foreground operators:
% 11.02/4.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.02/4.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.02/4.21  tff('#skF_11', type, '#skF_11': $i).
% 11.02/4.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.02/4.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.02/4.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.02/4.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.02/4.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.02/4.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.02/4.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.02/4.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.02/4.21  tff('#skF_10', type, '#skF_10': $i).
% 11.02/4.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.02/4.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.02/4.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.02/4.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.02/4.21  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 11.02/4.21  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 11.02/4.21  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 11.02/4.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.02/4.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.02/4.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.02/4.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.02/4.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.02/4.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.02/4.21  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 11.02/4.21  
% 11.02/4.22  tff(f_113, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 11.02/4.22  tff(f_100, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 11.02/4.22  tff(f_53, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.02/4.22  tff(f_78, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.02/4.22  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 11.02/4.22  tff(c_118, plain, ('#skF_11'!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.02/4.22  tff(c_100, plain, (![C_45]: (r2_hidden(C_45, k1_tarski(C_45)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.02/4.22  tff(c_120, plain, (k2_xboole_0(k1_tarski('#skF_10'), k1_tarski('#skF_11'))=k1_tarski('#skF_10')), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.02/4.22  tff(c_28, plain, (![D_19, A_14, B_15]: (r2_hidden(D_19, k4_xboole_0(A_14, B_15)) | r2_hidden(D_19, B_15) | ~r2_hidden(D_19, A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.02/4.22  tff(c_72, plain, (![A_32, B_33]: (k5_xboole_0(A_32, k4_xboole_0(B_33, A_32))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.02/4.22  tff(c_1425, plain, (![A_2769, B_2770, C_2771]: (r2_hidden(A_2769, B_2770) | ~r2_hidden(A_2769, C_2771) | r2_hidden(A_2769, k5_xboole_0(B_2770, C_2771)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.02/4.22  tff(c_29448, plain, (![A_17593, A_17594, B_17595]: (r2_hidden(A_17593, A_17594) | ~r2_hidden(A_17593, k4_xboole_0(B_17595, A_17594)) | r2_hidden(A_17593, k2_xboole_0(A_17594, B_17595)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1425])).
% 11.02/4.22  tff(c_34950, plain, (![D_19449, B_19450, A_19451]: (r2_hidden(D_19449, k2_xboole_0(B_19450, A_19451)) | r2_hidden(D_19449, B_19450) | ~r2_hidden(D_19449, A_19451))), inference(resolution, [status(thm)], [c_28, c_29448])).
% 11.02/4.22  tff(c_35499, plain, (![D_19709]: (r2_hidden(D_19709, k1_tarski('#skF_10')) | r2_hidden(D_19709, k1_tarski('#skF_10')) | ~r2_hidden(D_19709, k1_tarski('#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_120, c_34950])).
% 11.02/4.22  tff(c_35695, plain, (r2_hidden('#skF_11', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_100, c_35499])).
% 11.02/4.22  tff(c_98, plain, (![C_45, A_41]: (C_45=A_41 | ~r2_hidden(C_45, k1_tarski(A_41)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.02/4.22  tff(c_35702, plain, ('#skF_11'='#skF_10'), inference(resolution, [status(thm)], [c_35695, c_98])).
% 11.02/4.22  tff(c_35752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_35702])).
% 11.02/4.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.02/4.22  
% 11.02/4.22  Inference rules
% 11.02/4.22  ----------------------
% 11.02/4.22  #Ref     : 1
% 11.02/4.22  #Sup     : 6674
% 11.02/4.22  #Fact    : 2
% 11.02/4.22  #Define  : 0
% 11.02/4.22  #Split   : 5
% 11.02/4.22  #Chain   : 0
% 11.02/4.22  #Close   : 0
% 11.02/4.22  
% 11.02/4.22  Ordering : KBO
% 11.02/4.22  
% 11.02/4.22  Simplification rules
% 11.02/4.22  ----------------------
% 11.02/4.22  #Subsume      : 2094
% 11.02/4.22  #Demod        : 3928
% 11.02/4.22  #Tautology    : 1570
% 11.02/4.22  #SimpNegUnit  : 131
% 11.02/4.22  #BackRed      : 19
% 11.02/4.22  
% 11.02/4.22  #Partial instantiations: 8232
% 11.02/4.22  #Strategies tried      : 1
% 11.02/4.22  
% 11.02/4.22  Timing (in seconds)
% 11.02/4.22  ----------------------
% 11.02/4.22  Preprocessing        : 0.38
% 11.02/4.22  Parsing              : 0.19
% 11.02/4.22  CNF conversion       : 0.03
% 11.02/4.22  Main loop            : 3.04
% 11.02/4.22  Inferencing          : 0.96
% 11.02/4.22  Reduction            : 1.14
% 11.02/4.23  Demodulation         : 0.90
% 11.02/4.23  BG Simplification    : 0.12
% 11.02/4.23  Subsumption          : 0.60
% 11.02/4.23  Abstraction          : 0.19
% 11.02/4.23  MUC search           : 0.00
% 11.02/4.23  Cooper               : 0.00
% 11.02/4.23  Total                : 3.44
% 11.02/4.23  Index Insertion      : 0.00
% 11.02/4.23  Index Deletion       : 0.00
% 11.02/4.23  Index Matching       : 0.00
% 11.02/4.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
