%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:32 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  31 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_64,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_86,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_86])).

tff(c_128,plain,(
    ! [D_51,B_52,A_53] :
      ( r2_hidden(D_51,B_52)
      | ~ r2_hidden(D_51,k3_xboole_0(A_53,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_132,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_54,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_128])).

tff(c_137,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_132])).

tff(c_46,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_140,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_137,c_46])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:31:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.24  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 1.98/1.24  
% 1.98/1.24  %Foreground sorts:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Background operators:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Foreground operators:
% 1.98/1.24  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.98/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.24  tff('#skF_7', type, '#skF_7': $i).
% 1.98/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.98/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.98/1.24  tff('#skF_8', type, '#skF_8': $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.98/1.24  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.98/1.24  
% 1.98/1.25  tff(f_71, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.98/1.25  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.98/1.25  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.98/1.25  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.98/1.25  tff(c_64, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.98/1.25  tff(c_48, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.98/1.25  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.98/1.25  tff(c_86, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.98/1.25  tff(c_90, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_66, c_86])).
% 1.98/1.25  tff(c_128, plain, (![D_51, B_52, A_53]: (r2_hidden(D_51, B_52) | ~r2_hidden(D_51, k3_xboole_0(A_53, B_52)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.98/1.25  tff(c_132, plain, (![D_54]: (r2_hidden(D_54, k1_tarski('#skF_8')) | ~r2_hidden(D_54, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_128])).
% 1.98/1.25  tff(c_137, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_48, c_132])).
% 1.98/1.25  tff(c_46, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.98/1.25  tff(c_140, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_137, c_46])).
% 1.98/1.25  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_140])).
% 1.98/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  Inference rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Ref     : 0
% 1.98/1.25  #Sup     : 17
% 1.98/1.25  #Fact    : 0
% 1.98/1.25  #Define  : 0
% 1.98/1.25  #Split   : 0
% 1.98/1.25  #Chain   : 0
% 1.98/1.25  #Close   : 0
% 1.98/1.25  
% 1.98/1.25  Ordering : KBO
% 1.98/1.25  
% 1.98/1.25  Simplification rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Subsume      : 0
% 1.98/1.25  #Demod        : 3
% 1.98/1.25  #Tautology    : 11
% 1.98/1.25  #SimpNegUnit  : 1
% 1.98/1.25  #BackRed      : 0
% 1.98/1.25  
% 1.98/1.25  #Partial instantiations: 0
% 1.98/1.25  #Strategies tried      : 1
% 1.98/1.25  
% 1.98/1.25  Timing (in seconds)
% 1.98/1.25  ----------------------
% 2.03/1.25  Preprocessing        : 0.32
% 2.03/1.25  Parsing              : 0.16
% 2.03/1.25  CNF conversion       : 0.03
% 2.03/1.25  Main loop            : 0.13
% 2.03/1.25  Inferencing          : 0.03
% 2.03/1.25  Reduction            : 0.04
% 2.03/1.25  Demodulation         : 0.03
% 2.03/1.25  BG Simplification    : 0.02
% 2.03/1.25  Subsumption          : 0.03
% 2.03/1.25  Abstraction          : 0.01
% 2.03/1.25  MUC search           : 0.00
% 2.03/1.25  Cooper               : 0.00
% 2.03/1.25  Total                : 0.47
% 2.03/1.25  Index Insertion      : 0.00
% 2.03/1.25  Index Deletion       : 0.00
% 2.03/1.25  Index Matching       : 0.00
% 2.03/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
