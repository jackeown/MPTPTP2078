%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:22 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  26 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5

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

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_62,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_106,plain,(
    ! [D_40,B_41,A_42] :
      ( r2_hidden(D_40,B_41)
      | ~ r2_hidden(D_40,k3_xboole_0(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_125,plain,(
    ! [D_50] :
      ( r2_hidden(D_50,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_50,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_106])).

tff(c_130,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_46,c_125])).

tff(c_44,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_142,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_130,c_44])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 1.95/1.25  
% 1.95/1.25  %Foreground sorts:
% 1.95/1.25  
% 1.95/1.25  
% 1.95/1.25  %Background operators:
% 1.95/1.25  
% 1.95/1.25  
% 1.95/1.25  %Foreground operators:
% 1.95/1.25  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.95/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.25  tff('#skF_7', type, '#skF_7': $i).
% 1.95/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.95/1.25  tff('#skF_8', type, '#skF_8': $i).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.95/1.25  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.95/1.25  
% 1.95/1.26  tff(f_67, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.95/1.26  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.95/1.26  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.95/1.26  tff(c_62, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.95/1.26  tff(c_46, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.26  tff(c_64, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.95/1.26  tff(c_106, plain, (![D_40, B_41, A_42]: (r2_hidden(D_40, B_41) | ~r2_hidden(D_40, k3_xboole_0(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.95/1.26  tff(c_125, plain, (![D_50]: (r2_hidden(D_50, k1_tarski('#skF_8')) | ~r2_hidden(D_50, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_106])).
% 1.95/1.26  tff(c_130, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_46, c_125])).
% 1.95/1.26  tff(c_44, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.26  tff(c_142, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_130, c_44])).
% 1.95/1.26  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_142])).
% 1.95/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.26  
% 1.95/1.26  Inference rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Ref     : 0
% 1.95/1.26  #Sup     : 18
% 1.95/1.26  #Fact    : 0
% 1.95/1.26  #Define  : 0
% 1.95/1.26  #Split   : 0
% 1.95/1.26  #Chain   : 0
% 1.95/1.26  #Close   : 0
% 1.95/1.26  
% 1.95/1.26  Ordering : KBO
% 1.95/1.26  
% 1.95/1.26  Simplification rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Subsume      : 0
% 1.95/1.26  #Demod        : 3
% 1.95/1.26  #Tautology    : 13
% 1.95/1.26  #SimpNegUnit  : 1
% 1.95/1.26  #BackRed      : 0
% 1.95/1.26  
% 1.95/1.26  #Partial instantiations: 0
% 1.95/1.26  #Strategies tried      : 1
% 1.95/1.26  
% 1.95/1.26  Timing (in seconds)
% 1.95/1.26  ----------------------
% 1.95/1.26  Preprocessing        : 0.32
% 1.95/1.26  Parsing              : 0.16
% 1.95/1.26  CNF conversion       : 0.02
% 1.95/1.26  Main loop            : 0.13
% 1.95/1.27  Inferencing          : 0.03
% 1.95/1.27  Reduction            : 0.05
% 1.95/1.27  Demodulation         : 0.03
% 1.95/1.27  BG Simplification    : 0.01
% 1.95/1.27  Subsumption          : 0.03
% 1.95/1.27  Abstraction          : 0.01
% 1.95/1.27  MUC search           : 0.00
% 1.95/1.27  Cooper               : 0.00
% 1.95/1.27  Total                : 0.48
% 1.95/1.27  Index Insertion      : 0.00
% 1.95/1.27  Index Deletion       : 0.00
% 1.95/1.27  Index Matching       : 0.00
% 1.95/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
