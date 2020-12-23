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
% DateTime   : Thu Dec  3 09:48:26 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  42 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_32,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(k1_tarski(A_34),B_35)
      | r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(k1_tarski(A_34),B_35) = k1_tarski(A_34)
      | r2_hidden(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_84,c_6])).

tff(c_34,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_96,plain,(
    ! [A_37,B_38] : k5_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_105,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_96])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_108,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96])).

tff(c_148,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_108])).

tff(c_75,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [B_21] : ~ r1_xboole_0(k1_tarski(B_21),k1_tarski(B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_83,plain,(
    ! [B_21] : k4_xboole_0(k1_tarski(B_21),k1_tarski(B_21)) != k1_tarski(B_21) ),
    inference(resolution,[status(thm)],[c_75,c_30])).

tff(c_161,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_83])).

tff(c_174,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_161])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_177,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_174,c_10])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.30  
% 1.83/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.30  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.83/1.30  
% 1.83/1.30  %Foreground sorts:
% 1.83/1.30  
% 1.83/1.30  
% 1.83/1.30  %Background operators:
% 1.83/1.30  
% 1.83/1.30  
% 1.83/1.30  %Foreground operators:
% 1.83/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.83/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.83/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.83/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.83/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.83/1.30  
% 1.83/1.31  tff(f_61, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.83/1.31  tff(f_51, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.83/1.31  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.83/1.31  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.83/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.83/1.31  tff(f_56, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.83/1.31  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.83/1.31  tff(c_32, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.31  tff(c_84, plain, (![A_34, B_35]: (r1_xboole_0(k1_tarski(A_34), B_35) | r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.83/1.31  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.31  tff(c_92, plain, (![A_34, B_35]: (k4_xboole_0(k1_tarski(A_34), B_35)=k1_tarski(A_34) | r2_hidden(A_34, B_35))), inference(resolution, [status(thm)], [c_84, c_6])).
% 1.83/1.31  tff(c_34, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.31  tff(c_96, plain, (![A_37, B_38]: (k5_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.31  tff(c_105, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_96])).
% 1.83/1.31  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.31  tff(c_108, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_96])).
% 1.83/1.31  tff(c_148, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_108])).
% 1.83/1.31  tff(c_75, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k4_xboole_0(A_32, B_33)!=A_32)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.31  tff(c_30, plain, (![B_21]: (~r1_xboole_0(k1_tarski(B_21), k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.31  tff(c_83, plain, (![B_21]: (k4_xboole_0(k1_tarski(B_21), k1_tarski(B_21))!=k1_tarski(B_21))), inference(resolution, [status(thm)], [c_75, c_30])).
% 1.83/1.31  tff(c_161, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_148, c_83])).
% 1.83/1.31  tff(c_174, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_161])).
% 1.83/1.31  tff(c_10, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.31  tff(c_177, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_174, c_10])).
% 1.83/1.31  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_177])).
% 1.83/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.31  
% 1.83/1.31  Inference rules
% 1.83/1.31  ----------------------
% 1.83/1.31  #Ref     : 0
% 1.83/1.31  #Sup     : 35
% 1.83/1.31  #Fact    : 0
% 1.83/1.31  #Define  : 0
% 1.83/1.31  #Split   : 0
% 1.83/1.31  #Chain   : 0
% 1.83/1.31  #Close   : 0
% 1.83/1.31  
% 1.83/1.31  Ordering : KBO
% 1.83/1.31  
% 1.83/1.31  Simplification rules
% 1.83/1.31  ----------------------
% 1.83/1.31  #Subsume      : 0
% 1.83/1.31  #Demod        : 5
% 1.83/1.31  #Tautology    : 27
% 1.83/1.31  #SimpNegUnit  : 1
% 1.83/1.31  #BackRed      : 0
% 1.83/1.31  
% 1.83/1.31  #Partial instantiations: 0
% 1.83/1.31  #Strategies tried      : 1
% 1.83/1.31  
% 1.83/1.31  Timing (in seconds)
% 1.83/1.31  ----------------------
% 1.83/1.32  Preprocessing        : 0.32
% 1.83/1.32  Parsing              : 0.17
% 1.83/1.32  CNF conversion       : 0.02
% 1.83/1.32  Main loop            : 0.13
% 1.83/1.32  Inferencing          : 0.05
% 1.83/1.32  Reduction            : 0.04
% 1.83/1.32  Demodulation         : 0.03
% 1.83/1.32  BG Simplification    : 0.01
% 1.83/1.32  Subsumption          : 0.02
% 1.83/1.32  Abstraction          : 0.01
% 1.83/1.32  MUC search           : 0.00
% 1.83/1.32  Cooper               : 0.00
% 1.83/1.32  Total                : 0.47
% 1.83/1.32  Index Insertion      : 0.00
% 1.83/1.32  Index Deletion       : 0.00
% 1.83/1.32  Index Matching       : 0.00
% 1.83/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
