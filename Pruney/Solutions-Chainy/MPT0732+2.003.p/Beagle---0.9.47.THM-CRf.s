%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:02 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  44 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_ordinal1 > k3_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_ordinal1(C)
       => ( ( r2_hidden(A,B)
            & r2_hidden(B,C) )
         => r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_ordinal1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_28,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    v1_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_44,plain,(
    ! [B_20,A_21] :
      ( r1_tarski(B_20,A_21)
      | ~ r2_hidden(B_20,A_21)
      | ~ v1_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ v1_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_57,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_50])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_57,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [D_22] :
      ( r2_hidden(D_22,'#skF_6')
      | ~ r2_hidden(D_22,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_4])).

tff(c_78,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_85,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.26  
% 1.84/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.26  %$ r2_hidden > r1_tarski > v1_ordinal1 > k3_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.84/1.26  
% 1.84/1.26  %Foreground sorts:
% 1.84/1.26  
% 1.84/1.26  
% 1.84/1.26  %Background operators:
% 1.84/1.26  
% 1.84/1.26  
% 1.84/1.26  %Foreground operators:
% 1.84/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.84/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.26  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.84/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.26  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.26  tff('#skF_6', type, '#skF_6': $i).
% 1.84/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.84/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.26  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.84/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.26  
% 1.84/1.27  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_ordinal1(C) => ((r2_hidden(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_ordinal1)).
% 1.84/1.27  tff(f_45, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 1.84/1.27  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.84/1.27  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.84/1.27  tff(c_28, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.84/1.27  tff(c_32, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.84/1.27  tff(c_34, plain, (v1_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.84/1.27  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.84/1.27  tff(c_44, plain, (![B_20, A_21]: (r1_tarski(B_20, A_21) | ~r2_hidden(B_20, A_21) | ~v1_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.84/1.27  tff(c_50, plain, (r1_tarski('#skF_5', '#skF_6') | ~v1_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_44])).
% 1.84/1.27  tff(c_57, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_50])).
% 1.84/1.27  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.84/1.27  tff(c_63, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_57, c_20])).
% 1.84/1.27  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.84/1.27  tff(c_71, plain, (![D_22]: (r2_hidden(D_22, '#skF_6') | ~r2_hidden(D_22, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_4])).
% 1.84/1.27  tff(c_78, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_32, c_71])).
% 1.84/1.27  tff(c_85, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_78])).
% 1.84/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.27  
% 1.84/1.27  Inference rules
% 1.84/1.27  ----------------------
% 1.84/1.27  #Ref     : 0
% 1.84/1.27  #Sup     : 10
% 1.84/1.27  #Fact    : 0
% 1.84/1.27  #Define  : 0
% 1.84/1.27  #Split   : 1
% 1.84/1.27  #Chain   : 0
% 1.84/1.27  #Close   : 0
% 1.84/1.27  
% 1.84/1.27  Ordering : KBO
% 1.84/1.27  
% 1.84/1.27  Simplification rules
% 1.84/1.27  ----------------------
% 1.84/1.27  #Subsume      : 0
% 1.84/1.27  #Demod        : 1
% 1.84/1.27  #Tautology    : 3
% 1.84/1.27  #SimpNegUnit  : 2
% 1.84/1.27  #BackRed      : 0
% 1.84/1.27  
% 1.84/1.27  #Partial instantiations: 0
% 1.84/1.27  #Strategies tried      : 1
% 1.84/1.27  
% 1.84/1.27  Timing (in seconds)
% 1.84/1.27  ----------------------
% 1.84/1.27  Preprocessing        : 0.32
% 1.84/1.27  Parsing              : 0.17
% 1.84/1.27  CNF conversion       : 0.03
% 1.84/1.27  Main loop            : 0.11
% 1.84/1.27  Inferencing          : 0.04
% 1.84/1.27  Reduction            : 0.03
% 1.84/1.27  Demodulation         : 0.02
% 1.84/1.27  BG Simplification    : 0.02
% 1.84/1.27  Subsumption          : 0.02
% 1.84/1.27  Abstraction          : 0.01
% 1.84/1.27  MUC search           : 0.00
% 1.84/1.27  Cooper               : 0.00
% 1.84/1.27  Total                : 0.46
% 1.84/1.27  Index Insertion      : 0.00
% 1.84/1.28  Index Deletion       : 0.00
% 1.84/1.28  Index Matching       : 0.00
% 1.84/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
