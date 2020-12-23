%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:15 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  38 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_32,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    ! [A_25,B_26] : r1_tarski(k1_tarski(A_25),k2_tarski(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_149,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_196,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,k1_tarski('#skF_5'))
      | ~ r1_tarski(A_54,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_34,c_149])).

tff(c_206,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_30,c_196])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_213,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_206,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_168,plain,(
    ! [B_49,A_50] :
      ( r2_hidden(B_49,A_50)
      | k3_xboole_0(A_50,k1_tarski(B_49)) != k1_tarski(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_230,plain,(
    ! [B_56,B_57] :
      ( r2_hidden(B_56,B_57)
      | k3_xboole_0(k1_tarski(B_56),B_57) != k1_tarski(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_168])).

tff(c_248,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_230])).

tff(c_8,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_263,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_248,c_8])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.27  
% 1.85/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.16/1.27  
% 2.16/1.27  %Foreground sorts:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Background operators:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Foreground operators:
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.27  
% 2.16/1.28  tff(f_63, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.16/1.28  tff(f_58, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.16/1.28  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.16/1.28  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.16/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.16/1.28  tff(f_56, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.16/1.28  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.16/1.28  tff(c_32, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.28  tff(c_30, plain, (![A_25, B_26]: (r1_tarski(k1_tarski(A_25), k2_tarski(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.16/1.28  tff(c_34, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.28  tff(c_149, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.28  tff(c_196, plain, (![A_54]: (r1_tarski(A_54, k1_tarski('#skF_5')) | ~r1_tarski(A_54, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_34, c_149])).
% 2.16/1.28  tff(c_206, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_196])).
% 2.16/1.28  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.28  tff(c_213, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_206, c_6])).
% 2.16/1.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.28  tff(c_168, plain, (![B_49, A_50]: (r2_hidden(B_49, A_50) | k3_xboole_0(A_50, k1_tarski(B_49))!=k1_tarski(B_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.28  tff(c_230, plain, (![B_56, B_57]: (r2_hidden(B_56, B_57) | k3_xboole_0(k1_tarski(B_56), B_57)!=k1_tarski(B_56))), inference(superposition, [status(thm), theory('equality')], [c_2, c_168])).
% 2.16/1.28  tff(c_248, plain, (r2_hidden('#skF_3', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_230])).
% 2.16/1.28  tff(c_8, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.16/1.28  tff(c_263, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_248, c_8])).
% 2.16/1.28  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_263])).
% 2.16/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.28  
% 2.16/1.28  Inference rules
% 2.16/1.28  ----------------------
% 2.16/1.28  #Ref     : 0
% 2.16/1.28  #Sup     : 57
% 2.16/1.28  #Fact    : 0
% 2.16/1.28  #Define  : 0
% 2.16/1.28  #Split   : 1
% 2.16/1.28  #Chain   : 0
% 2.16/1.28  #Close   : 0
% 2.16/1.28  
% 2.16/1.28  Ordering : KBO
% 2.16/1.28  
% 2.16/1.28  Simplification rules
% 2.16/1.28  ----------------------
% 2.16/1.28  #Subsume      : 3
% 2.16/1.28  #Demod        : 3
% 2.16/1.28  #Tautology    : 30
% 2.16/1.28  #SimpNegUnit  : 1
% 2.16/1.28  #BackRed      : 0
% 2.16/1.28  
% 2.16/1.28  #Partial instantiations: 0
% 2.16/1.28  #Strategies tried      : 1
% 2.16/1.28  
% 2.16/1.28  Timing (in seconds)
% 2.16/1.28  ----------------------
% 2.16/1.28  Preprocessing        : 0.31
% 2.16/1.28  Parsing              : 0.16
% 2.16/1.28  CNF conversion       : 0.02
% 2.16/1.28  Main loop            : 0.19
% 2.16/1.28  Inferencing          : 0.07
% 2.16/1.28  Reduction            : 0.06
% 2.16/1.28  Demodulation         : 0.05
% 2.16/1.28  BG Simplification    : 0.01
% 2.16/1.28  Subsumption          : 0.04
% 2.16/1.28  Abstraction          : 0.01
% 2.16/1.28  MUC search           : 0.00
% 2.16/1.28  Cooper               : 0.00
% 2.16/1.28  Total                : 0.53
% 2.16/1.28  Index Insertion      : 0.00
% 2.16/1.28  Index Deletion       : 0.00
% 2.16/1.28  Index Matching       : 0.00
% 2.16/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
