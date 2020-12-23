%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:55 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   36 (  46 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   38 (  60 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_46,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_36,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_27,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_mcart_1(k4_tarski(A_10,B_11)) = B_11 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [B_6,C_7] : k2_mcart_1(k4_tarski(B_6,C_7)) != k4_tarski(B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [B_6,C_7] : k4_tarski(B_6,C_7) != C_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4])).

tff(c_2,plain,(
    ! [A_1,B_2] : v1_relat_1(k2_zfmisc_1(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_mcart_1(k4_tarski(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [B_6,C_7] : k1_mcart_1(k4_tarski(B_6,C_7)) != k4_tarski(B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_17,plain,(
    ! [B_6,C_7] : k4_tarski(B_6,C_7) != B_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6])).

tff(c_14,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_16,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_45,plain,(
    ! [A_22,B_23] :
      ( k4_tarski(k1_mcart_1(A_22),k2_mcart_1(A_22)) = A_22
      | ~ r2_hidden(A_22,B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,
    ( k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_45])).

tff(c_50,plain,(
    k4_tarski('#skF_1',k2_mcart_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40,c_47])).

tff(c_52,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17,c_50])).

tff(c_53,plain,(
    k2_mcart_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_59,plain,(
    ! [A_24,B_25] :
      ( k4_tarski(k1_mcart_1(A_24),k2_mcart_1(A_24)) = A_24
      | ~ r2_hidden(A_24,B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61,plain,
    ( k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_59])).

tff(c_64,plain,(
    k4_tarski(k1_mcart_1('#skF_1'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_53,c_61])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.19  
% 1.74/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.19  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.74/1.19  
% 1.74/1.19  %Foreground sorts:
% 1.74/1.19  
% 1.74/1.19  
% 1.74/1.19  %Background operators:
% 1.74/1.19  
% 1.74/1.19  
% 1.74/1.19  %Foreground operators:
% 1.74/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.74/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.19  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.74/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.74/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.19  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.74/1.19  
% 1.74/1.20  tff(f_46, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.74/1.20  tff(f_36, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.74/1.20  tff(f_27, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.74/1.20  tff(f_55, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_mcart_1)).
% 1.74/1.20  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.74/1.20  tff(c_12, plain, (![A_10, B_11]: (k2_mcart_1(k4_tarski(A_10, B_11))=B_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.74/1.20  tff(c_4, plain, (![B_6, C_7]: (k2_mcart_1(k4_tarski(B_6, C_7))!=k4_tarski(B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.74/1.20  tff(c_18, plain, (![B_6, C_7]: (k4_tarski(B_6, C_7)!=C_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4])).
% 1.74/1.20  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.74/1.20  tff(c_10, plain, (![A_10, B_11]: (k1_mcart_1(k4_tarski(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.74/1.20  tff(c_6, plain, (![B_6, C_7]: (k1_mcart_1(k4_tarski(B_6, C_7))!=k4_tarski(B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.74/1.20  tff(c_17, plain, (![B_6, C_7]: (k4_tarski(B_6, C_7)!=B_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6])).
% 1.74/1.20  tff(c_14, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.74/1.20  tff(c_40, plain, (k1_mcart_1('#skF_1')='#skF_1'), inference(splitLeft, [status(thm)], [c_14])).
% 1.74/1.20  tff(c_16, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.74/1.20  tff(c_45, plain, (![A_22, B_23]: (k4_tarski(k1_mcart_1(A_22), k2_mcart_1(A_22))=A_22 | ~r2_hidden(A_22, B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.20  tff(c_47, plain, (k4_tarski(k1_mcart_1('#skF_1'), k2_mcart_1('#skF_1'))='#skF_1' | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_45])).
% 1.74/1.20  tff(c_50, plain, (k4_tarski('#skF_1', k2_mcart_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40, c_47])).
% 1.74/1.20  tff(c_52, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17, c_50])).
% 1.74/1.20  tff(c_53, plain, (k2_mcart_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_14])).
% 1.74/1.20  tff(c_59, plain, (![A_24, B_25]: (k4_tarski(k1_mcart_1(A_24), k2_mcart_1(A_24))=A_24 | ~r2_hidden(A_24, B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.20  tff(c_61, plain, (k4_tarski(k1_mcart_1('#skF_1'), k2_mcart_1('#skF_1'))='#skF_1' | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_59])).
% 1.74/1.20  tff(c_64, plain, (k4_tarski(k1_mcart_1('#skF_1'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_53, c_61])).
% 1.74/1.20  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_64])).
% 1.74/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.20  
% 1.74/1.20  Inference rules
% 1.74/1.20  ----------------------
% 1.74/1.20  #Ref     : 0
% 1.74/1.20  #Sup     : 10
% 1.74/1.20  #Fact    : 0
% 1.74/1.20  #Define  : 0
% 1.74/1.20  #Split   : 1
% 1.74/1.20  #Chain   : 0
% 1.74/1.20  #Close   : 0
% 1.74/1.20  
% 1.74/1.20  Ordering : KBO
% 1.74/1.20  
% 1.74/1.20  Simplification rules
% 1.74/1.20  ----------------------
% 1.74/1.20  #Subsume      : 0
% 1.74/1.20  #Demod        : 6
% 1.74/1.20  #Tautology    : 8
% 1.74/1.20  #SimpNegUnit  : 2
% 1.74/1.20  #BackRed      : 0
% 1.74/1.20  
% 1.74/1.20  #Partial instantiations: 0
% 1.74/1.20  #Strategies tried      : 1
% 1.74/1.20  
% 1.74/1.20  Timing (in seconds)
% 1.74/1.20  ----------------------
% 1.74/1.21  Preprocessing        : 0.24
% 1.74/1.21  Parsing              : 0.13
% 1.74/1.21  CNF conversion       : 0.02
% 1.74/1.21  Main loop            : 0.11
% 1.74/1.21  Inferencing          : 0.04
% 1.74/1.21  Reduction            : 0.03
% 1.74/1.21  Demodulation         : 0.03
% 1.74/1.21  BG Simplification    : 0.01
% 1.74/1.21  Subsumption          : 0.02
% 1.74/1.21  Abstraction          : 0.00
% 1.74/1.21  MUC search           : 0.00
% 1.74/1.21  Cooper               : 0.00
% 1.74/1.21  Total                : 0.39
% 1.74/1.21  Index Insertion      : 0.00
% 1.74/1.21  Index Deletion       : 0.00
% 1.74/1.21  Index Matching       : 0.00
% 1.74/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
