%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:25 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   37 (  50 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  80 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r2_hidden(B,A)
           => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
              & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_14,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_3'),k2_relat_1('#skF_2'))
    | ~ r2_hidden(k1_mcart_1('#skF_3'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_3'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,k2_zfmisc_1(k1_relat_1(A_6),k2_relat_1(A_6)))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [B_26] :
      ( r2_hidden('#skF_3',B_26)
      | ~ r1_tarski('#skF_2',B_26) ) ),
    inference(resolution,[status(thm)],[c_16,c_38])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden(k1_mcart_1(A_7),B_8)
      | ~ r2_hidden(A_7,k2_zfmisc_1(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_104,plain,(
    ! [B_35,C_36] :
      ( r2_hidden(k1_mcart_1('#skF_3'),B_35)
      | ~ r1_tarski('#skF_2',k2_zfmisc_1(B_35,C_36)) ) ),
    inference(resolution,[status(thm)],[c_46,c_12])).

tff(c_107,plain,
    ( r2_hidden(k1_mcart_1('#skF_3'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_104])).

tff(c_110,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_107])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_110])).

tff(c_113,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_118,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_3',B_37)
      | ~ r1_tarski('#skF_2',B_37) ) ),
    inference(resolution,[status(thm)],[c_16,c_38])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8] :
      ( r2_hidden(k2_mcart_1(A_7),C_9)
      | ~ r2_hidden(A_7,k2_zfmisc_1(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_156,plain,(
    ! [C_43,B_44] :
      ( r2_hidden(k2_mcart_1('#skF_3'),C_43)
      | ~ r1_tarski('#skF_2',k2_zfmisc_1(B_44,C_43)) ) ),
    inference(resolution,[status(thm)],[c_118,c_10])).

tff(c_159,plain,
    ( r2_hidden(k2_mcart_1('#skF_3'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_156])).

tff(c_162,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_159])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:08:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.23  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.94/1.23  
% 1.94/1.23  %Foreground sorts:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Background operators:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Foreground operators:
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.23  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.94/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.23  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.94/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.23  
% 1.94/1.24  tff(f_52, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => (r2_hidden(k1_mcart_1(B), k1_relat_1(A)) & r2_hidden(k2_mcart_1(B), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_mcart_1)).
% 1.94/1.24  tff(f_36, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 1.94/1.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.94/1.24  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.94/1.24  tff(c_14, plain, (~r2_hidden(k2_mcart_1('#skF_3'), k2_relat_1('#skF_2')) | ~r2_hidden(k1_mcart_1('#skF_3'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.24  tff(c_45, plain, (~r2_hidden(k1_mcart_1('#skF_3'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_14])).
% 1.94/1.24  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.24  tff(c_8, plain, (![A_6]: (r1_tarski(A_6, k2_zfmisc_1(k1_relat_1(A_6), k2_relat_1(A_6))) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.94/1.24  tff(c_16, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.24  tff(c_38, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.24  tff(c_46, plain, (![B_26]: (r2_hidden('#skF_3', B_26) | ~r1_tarski('#skF_2', B_26))), inference(resolution, [status(thm)], [c_16, c_38])).
% 1.94/1.24  tff(c_12, plain, (![A_7, B_8, C_9]: (r2_hidden(k1_mcart_1(A_7), B_8) | ~r2_hidden(A_7, k2_zfmisc_1(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.94/1.24  tff(c_104, plain, (![B_35, C_36]: (r2_hidden(k1_mcart_1('#skF_3'), B_35) | ~r1_tarski('#skF_2', k2_zfmisc_1(B_35, C_36)))), inference(resolution, [status(thm)], [c_46, c_12])).
% 1.94/1.24  tff(c_107, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_104])).
% 1.94/1.24  tff(c_110, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_107])).
% 1.94/1.24  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_110])).
% 1.94/1.24  tff(c_113, plain, (~r2_hidden(k2_mcart_1('#skF_3'), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_14])).
% 1.94/1.24  tff(c_118, plain, (![B_37]: (r2_hidden('#skF_3', B_37) | ~r1_tarski('#skF_2', B_37))), inference(resolution, [status(thm)], [c_16, c_38])).
% 1.94/1.24  tff(c_10, plain, (![A_7, C_9, B_8]: (r2_hidden(k2_mcart_1(A_7), C_9) | ~r2_hidden(A_7, k2_zfmisc_1(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.94/1.24  tff(c_156, plain, (![C_43, B_44]: (r2_hidden(k2_mcart_1('#skF_3'), C_43) | ~r1_tarski('#skF_2', k2_zfmisc_1(B_44, C_43)))), inference(resolution, [status(thm)], [c_118, c_10])).
% 1.94/1.24  tff(c_159, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_156])).
% 1.94/1.24  tff(c_162, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_159])).
% 1.94/1.24  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_162])).
% 1.94/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  Inference rules
% 1.94/1.24  ----------------------
% 1.94/1.24  #Ref     : 0
% 1.94/1.24  #Sup     : 31
% 1.94/1.24  #Fact    : 0
% 1.94/1.24  #Define  : 0
% 1.94/1.24  #Split   : 1
% 1.94/1.24  #Chain   : 0
% 1.94/1.24  #Close   : 0
% 1.94/1.24  
% 1.94/1.24  Ordering : KBO
% 1.94/1.24  
% 1.94/1.24  Simplification rules
% 1.94/1.24  ----------------------
% 1.94/1.24  #Subsume      : 2
% 1.94/1.24  #Demod        : 5
% 1.94/1.24  #Tautology    : 2
% 1.94/1.24  #SimpNegUnit  : 2
% 1.94/1.24  #BackRed      : 0
% 1.94/1.24  
% 1.94/1.24  #Partial instantiations: 0
% 1.94/1.24  #Strategies tried      : 1
% 1.94/1.24  
% 1.94/1.24  Timing (in seconds)
% 1.94/1.24  ----------------------
% 1.94/1.24  Preprocessing        : 0.26
% 1.94/1.24  Parsing              : 0.15
% 1.94/1.24  CNF conversion       : 0.02
% 1.94/1.24  Main loop            : 0.18
% 1.94/1.24  Inferencing          : 0.07
% 1.94/1.24  Reduction            : 0.04
% 1.94/1.24  Demodulation         : 0.03
% 1.94/1.24  BG Simplification    : 0.01
% 1.94/1.24  Subsumption          : 0.04
% 1.94/1.24  Abstraction          : 0.01
% 1.94/1.24  MUC search           : 0.00
% 1.94/1.24  Cooper               : 0.00
% 1.94/1.24  Total                : 0.46
% 1.94/1.24  Index Insertion      : 0.00
% 1.94/1.24  Index Deletion       : 0.00
% 1.94/1.24  Index Matching       : 0.00
% 1.94/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
