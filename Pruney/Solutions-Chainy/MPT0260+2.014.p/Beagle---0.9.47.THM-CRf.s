%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:11 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  45 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_32,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    r1_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_37,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(B_20,A_21)
      | ~ r1_xboole_0(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    r1_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_37])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(k1_tarski(A_14),B_15) = B_15
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_59,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_xboole_0(A_29,B_30)
      | ~ r1_xboole_0(A_29,k2_xboole_0(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [A_35,A_36,B_37] :
      ( r1_xboole_0(A_35,k1_tarski(A_36))
      | ~ r1_xboole_0(A_35,B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_59])).

tff(c_81,plain,(
    ! [A_38] :
      ( r1_xboole_0('#skF_5',k1_tarski(A_38))
      | ~ r2_hidden(A_38,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_40,c_74])).

tff(c_91,plain,(
    r1_xboole_0('#skF_5',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_81])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    r1_xboole_0(k1_tarski('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden(A_12,B_13)
      | ~ r1_xboole_0(k1_tarski(A_12),B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_142,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_28])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:47:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  %$ r2_hidden > r1_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.80/1.17  
% 1.80/1.17  %Foreground sorts:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Background operators:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Foreground operators:
% 1.80/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.80/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.80/1.17  
% 1.80/1.18  tff(f_69, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.80/1.18  tff(f_54, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.80/1.18  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.80/1.18  tff(f_63, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.80/1.18  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.80/1.18  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.80/1.18  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.80/1.18  tff(c_14, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.80/1.18  tff(c_34, plain, (r1_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.80/1.18  tff(c_37, plain, (![B_20, A_21]: (r1_xboole_0(B_20, A_21) | ~r1_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.18  tff(c_40, plain, (r1_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_37])).
% 1.80/1.18  tff(c_30, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), B_15)=B_15 | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.80/1.18  tff(c_59, plain, (![A_29, B_30, C_31]: (r1_xboole_0(A_29, B_30) | ~r1_xboole_0(A_29, k2_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.80/1.18  tff(c_74, plain, (![A_35, A_36, B_37]: (r1_xboole_0(A_35, k1_tarski(A_36)) | ~r1_xboole_0(A_35, B_37) | ~r2_hidden(A_36, B_37))), inference(superposition, [status(thm), theory('equality')], [c_30, c_59])).
% 1.80/1.18  tff(c_81, plain, (![A_38]: (r1_xboole_0('#skF_5', k1_tarski(A_38)) | ~r2_hidden(A_38, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_40, c_74])).
% 1.80/1.18  tff(c_91, plain, (r1_xboole_0('#skF_5', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_81])).
% 1.80/1.18  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.18  tff(c_103, plain, (r1_xboole_0(k1_tarski('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_91, c_2])).
% 1.80/1.18  tff(c_28, plain, (![A_12, B_13]: (~r2_hidden(A_12, B_13) | ~r1_xboole_0(k1_tarski(A_12), B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.80/1.18  tff(c_142, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_103, c_28])).
% 1.80/1.18  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_142])).
% 1.80/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  
% 1.80/1.18  Inference rules
% 1.80/1.18  ----------------------
% 1.80/1.18  #Ref     : 0
% 1.80/1.18  #Sup     : 28
% 1.80/1.18  #Fact    : 0
% 1.80/1.18  #Define  : 0
% 1.80/1.18  #Split   : 0
% 1.80/1.18  #Chain   : 0
% 1.80/1.18  #Close   : 0
% 1.80/1.18  
% 1.80/1.18  Ordering : KBO
% 1.80/1.18  
% 1.80/1.18  Simplification rules
% 1.80/1.18  ----------------------
% 1.80/1.18  #Subsume      : 0
% 1.80/1.18  #Demod        : 3
% 1.80/1.18  #Tautology    : 10
% 1.80/1.18  #SimpNegUnit  : 0
% 1.80/1.18  #BackRed      : 0
% 1.80/1.18  
% 1.80/1.18  #Partial instantiations: 0
% 1.80/1.18  #Strategies tried      : 1
% 1.80/1.18  
% 1.80/1.18  Timing (in seconds)
% 1.80/1.18  ----------------------
% 1.80/1.18  Preprocessing        : 0.28
% 1.80/1.18  Parsing              : 0.15
% 1.80/1.18  CNF conversion       : 0.02
% 1.80/1.18  Main loop            : 0.15
% 1.80/1.18  Inferencing          : 0.05
% 1.80/1.18  Reduction            : 0.04
% 1.80/1.18  Demodulation         : 0.03
% 1.80/1.18  BG Simplification    : 0.01
% 1.80/1.18  Subsumption          : 0.04
% 1.80/1.18  Abstraction          : 0.01
% 1.80/1.18  MUC search           : 0.00
% 1.80/1.18  Cooper               : 0.00
% 1.80/1.18  Total                : 0.45
% 1.80/1.18  Index Insertion      : 0.00
% 1.80/1.18  Index Deletion       : 0.00
% 1.80/1.18  Index Matching       : 0.00
% 1.80/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
