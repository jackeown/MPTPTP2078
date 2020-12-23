%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:30 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  41 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,(
    ! [D_22,B_23,A_24] :
      ( ~ r2_hidden(D_22,B_23)
      | ~ r2_hidden(D_22,k4_xboole_0(A_24,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    ! [A_40,A_41,B_42] :
      ( ~ r2_hidden('#skF_3'(A_40,k4_xboole_0(A_41,B_42)),B_42)
      | r1_xboole_0(A_40,k4_xboole_0(A_41,B_42)) ) ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_106,plain,(
    ! [A_45,A_46] : r1_xboole_0(A_45,k4_xboole_0(A_46,A_45)) ),
    inference(resolution,[status(thm)],[c_24,c_82])).

tff(c_26,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_xboole_0(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_194,plain,(
    ! [A_56,A_57,A_58] :
      ( r1_xboole_0(A_56,k4_xboole_0(A_57,A_58))
      | ~ r1_tarski(A_56,A_58) ) ),
    inference(resolution,[status(thm)],[c_106,c_26])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_4',k4_xboole_0('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_201,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_194,c_28])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:49:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.23  
% 1.87/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.87/1.23  
% 1.87/1.23  %Foreground sorts:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Background operators:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Foreground operators:
% 1.87/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.87/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.87/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.23  
% 1.87/1.24  tff(f_64, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.87/1.24  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.87/1.24  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.87/1.24  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.87/1.24  tff(c_30, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.87/1.24  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.87/1.24  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.87/1.24  tff(c_44, plain, (![D_22, B_23, A_24]: (~r2_hidden(D_22, B_23) | ~r2_hidden(D_22, k4_xboole_0(A_24, B_23)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.24  tff(c_82, plain, (![A_40, A_41, B_42]: (~r2_hidden('#skF_3'(A_40, k4_xboole_0(A_41, B_42)), B_42) | r1_xboole_0(A_40, k4_xboole_0(A_41, B_42)))), inference(resolution, [status(thm)], [c_22, c_44])).
% 1.87/1.24  tff(c_106, plain, (![A_45, A_46]: (r1_xboole_0(A_45, k4_xboole_0(A_46, A_45)))), inference(resolution, [status(thm)], [c_24, c_82])).
% 1.87/1.24  tff(c_26, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, C_14) | ~r1_xboole_0(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.87/1.24  tff(c_194, plain, (![A_56, A_57, A_58]: (r1_xboole_0(A_56, k4_xboole_0(A_57, A_58)) | ~r1_tarski(A_56, A_58))), inference(resolution, [status(thm)], [c_106, c_26])).
% 1.87/1.24  tff(c_28, plain, (~r1_xboole_0('#skF_4', k4_xboole_0('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.87/1.24  tff(c_201, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_194, c_28])).
% 1.87/1.24  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_201])).
% 1.87/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.24  
% 1.87/1.24  Inference rules
% 1.87/1.24  ----------------------
% 1.87/1.24  #Ref     : 0
% 1.87/1.24  #Sup     : 36
% 1.87/1.24  #Fact    : 0
% 1.87/1.24  #Define  : 0
% 1.87/1.24  #Split   : 0
% 1.87/1.24  #Chain   : 0
% 1.87/1.24  #Close   : 0
% 1.87/1.24  
% 1.87/1.24  Ordering : KBO
% 1.87/1.24  
% 1.87/1.24  Simplification rules
% 1.87/1.24  ----------------------
% 1.87/1.24  #Subsume      : 2
% 1.87/1.24  #Demod        : 3
% 1.87/1.24  #Tautology    : 6
% 1.87/1.24  #SimpNegUnit  : 0
% 1.87/1.24  #BackRed      : 0
% 1.87/1.24  
% 1.87/1.24  #Partial instantiations: 0
% 1.87/1.24  #Strategies tried      : 1
% 1.87/1.24  
% 1.87/1.24  Timing (in seconds)
% 1.87/1.24  ----------------------
% 1.87/1.25  Preprocessing        : 0.26
% 1.87/1.25  Parsing              : 0.14
% 1.87/1.25  CNF conversion       : 0.02
% 1.87/1.25  Main loop            : 0.17
% 1.87/1.25  Inferencing          : 0.07
% 1.87/1.25  Reduction            : 0.04
% 1.87/1.25  Demodulation         : 0.03
% 1.87/1.25  BG Simplification    : 0.02
% 1.87/1.25  Subsumption          : 0.04
% 1.87/1.25  Abstraction          : 0.01
% 1.87/1.25  MUC search           : 0.00
% 1.87/1.25  Cooper               : 0.00
% 1.87/1.25  Total                : 0.46
% 1.87/1.25  Index Insertion      : 0.00
% 1.87/1.25  Index Deletion       : 0.00
% 1.87/1.25  Index Matching       : 0.00
% 1.87/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
