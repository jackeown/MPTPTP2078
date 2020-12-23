%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:48 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  35 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_28,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_84,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_xboole_0(k2_tarski(A_58,C_59),B_60)
      | r2_hidden(C_59,B_60)
      | r2_hidden(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [B_61,A_62,C_63] :
      ( r1_xboole_0(B_61,k2_tarski(A_62,C_63))
      | r2_hidden(C_63,B_61)
      | r2_hidden(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [B_64,A_65,C_66] :
      ( k4_xboole_0(B_64,k2_tarski(A_65,C_66)) = B_64
      | r2_hidden(C_66,B_64)
      | r2_hidden(A_65,B_64) ) ),
    inference(resolution,[status(thm)],[c_92,c_6])).

tff(c_24,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_108,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_24])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:53:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.15  
% 1.67/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.15  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.67/1.15  
% 1.67/1.15  %Foreground sorts:
% 1.67/1.15  
% 1.67/1.15  
% 1.67/1.15  %Background operators:
% 1.67/1.15  
% 1.67/1.15  
% 1.67/1.15  %Foreground operators:
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.67/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.67/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.67/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.67/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.67/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.15  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.15  
% 1.67/1.16  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 1.67/1.16  tff(f_57, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 1.67/1.16  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.67/1.16  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.67/1.16  tff(c_28, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.67/1.16  tff(c_26, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.67/1.16  tff(c_84, plain, (![A_58, C_59, B_60]: (r1_xboole_0(k2_tarski(A_58, C_59), B_60) | r2_hidden(C_59, B_60) | r2_hidden(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.67/1.16  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.16  tff(c_92, plain, (![B_61, A_62, C_63]: (r1_xboole_0(B_61, k2_tarski(A_62, C_63)) | r2_hidden(C_63, B_61) | r2_hidden(A_62, B_61))), inference(resolution, [status(thm)], [c_84, c_2])).
% 1.67/1.16  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.16  tff(c_100, plain, (![B_64, A_65, C_66]: (k4_xboole_0(B_64, k2_tarski(A_65, C_66))=B_64 | r2_hidden(C_66, B_64) | r2_hidden(A_65, B_64))), inference(resolution, [status(thm)], [c_92, c_6])).
% 1.67/1.16  tff(c_24, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.67/1.16  tff(c_108, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_100, c_24])).
% 1.67/1.16  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_108])).
% 1.67/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  
% 1.67/1.16  Inference rules
% 1.67/1.16  ----------------------
% 1.67/1.16  #Ref     : 0
% 1.67/1.16  #Sup     : 20
% 1.67/1.16  #Fact    : 0
% 1.67/1.16  #Define  : 0
% 1.67/1.16  #Split   : 0
% 1.67/1.16  #Chain   : 0
% 1.67/1.16  #Close   : 0
% 1.67/1.16  
% 1.67/1.16  Ordering : KBO
% 1.67/1.16  
% 1.67/1.16  Simplification rules
% 1.67/1.16  ----------------------
% 1.67/1.16  #Subsume      : 2
% 1.67/1.16  #Demod        : 0
% 1.67/1.16  #Tautology    : 10
% 1.67/1.16  #SimpNegUnit  : 1
% 1.67/1.16  #BackRed      : 0
% 1.67/1.16  
% 1.67/1.16  #Partial instantiations: 0
% 1.67/1.16  #Strategies tried      : 1
% 1.67/1.16  
% 1.67/1.16  Timing (in seconds)
% 1.67/1.16  ----------------------
% 1.67/1.16  Preprocessing        : 0.30
% 1.67/1.16  Parsing              : 0.16
% 1.67/1.16  CNF conversion       : 0.02
% 1.67/1.16  Main loop            : 0.11
% 1.67/1.16  Inferencing          : 0.05
% 1.67/1.16  Reduction            : 0.03
% 1.67/1.16  Demodulation         : 0.02
% 1.67/1.16  BG Simplification    : 0.01
% 1.67/1.16  Subsumption          : 0.02
% 1.67/1.16  Abstraction          : 0.01
% 1.67/1.16  MUC search           : 0.00
% 1.67/1.16  Cooper               : 0.00
% 1.67/1.16  Total                : 0.43
% 1.67/1.16  Index Insertion      : 0.00
% 1.67/1.16  Index Deletion       : 0.00
% 1.67/1.16  Index Matching       : 0.00
% 1.67/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
