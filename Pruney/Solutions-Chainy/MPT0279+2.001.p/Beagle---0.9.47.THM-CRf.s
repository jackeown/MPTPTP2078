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
% DateTime   : Thu Dec  3 09:53:23 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   36 (  39 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  43 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    ! [C_24,A_20] :
      ( r2_hidden(C_24,k1_zfmisc_1(A_20))
      | ~ r1_tarski(C_24,A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_112,plain,(
    ! [D_44,B_45,A_46] :
      ( D_44 = B_45
      | D_44 = A_46
      | ~ r2_hidden(D_44,k2_tarski(A_46,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_131,plain,(
    ! [D_47,A_48] :
      ( D_47 = A_48
      | D_47 = A_48
      | ~ r2_hidden(D_47,k1_tarski(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_112])).

tff(c_194,plain,(
    ! [A_63,B_64] :
      ( '#skF_1'(k1_tarski(A_63),B_64) = A_63
      | r1_tarski(k1_tarski(A_63),B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_205,plain,(
    '#skF_1'(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_194,c_50])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_212,plain,
    ( ~ r2_hidden('#skF_6',k1_zfmisc_1('#skF_6'))
    | r1_tarski(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_4])).

tff(c_217,plain,(
    ~ r2_hidden('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_212])).

tff(c_221,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_217])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 1.91/1.19  
% 1.91/1.19  %Foreground sorts:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Background operators:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Foreground operators:
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.19  tff('#skF_6', type, '#skF_6': $i).
% 1.91/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.19  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.91/1.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.91/1.19  
% 1.91/1.19  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.91/1.19  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.91/1.19  tff(f_63, negated_conjecture, ~(![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 1.91/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.91/1.19  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.91/1.19  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.91/1.19  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.19  tff(c_40, plain, (![C_24, A_20]: (r2_hidden(C_24, k1_zfmisc_1(A_20)) | ~r1_tarski(C_24, A_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.19  tff(c_50, plain, (~r1_tarski(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.19  tff(c_32, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.91/1.19  tff(c_112, plain, (![D_44, B_45, A_46]: (D_44=B_45 | D_44=A_46 | ~r2_hidden(D_44, k2_tarski(A_46, B_45)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.19  tff(c_131, plain, (![D_47, A_48]: (D_47=A_48 | D_47=A_48 | ~r2_hidden(D_47, k1_tarski(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_112])).
% 1.91/1.19  tff(c_194, plain, (![A_63, B_64]: ('#skF_1'(k1_tarski(A_63), B_64)=A_63 | r1_tarski(k1_tarski(A_63), B_64))), inference(resolution, [status(thm)], [c_6, c_131])).
% 1.91/1.19  tff(c_205, plain, ('#skF_1'(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_194, c_50])).
% 1.91/1.19  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.19  tff(c_212, plain, (~r2_hidden('#skF_6', k1_zfmisc_1('#skF_6')) | r1_tarski(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_205, c_4])).
% 1.91/1.19  tff(c_217, plain, (~r2_hidden('#skF_6', k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_50, c_212])).
% 1.91/1.19  tff(c_221, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_217])).
% 1.91/1.19  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_221])).
% 1.91/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  Inference rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Ref     : 0
% 1.91/1.19  #Sup     : 37
% 1.91/1.19  #Fact    : 0
% 1.91/1.19  #Define  : 0
% 1.91/1.20  #Split   : 0
% 1.91/1.20  #Chain   : 0
% 1.91/1.20  #Close   : 0
% 1.91/1.20  
% 1.91/1.20  Ordering : KBO
% 1.91/1.20  
% 1.91/1.20  Simplification rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Subsume      : 2
% 1.91/1.20  #Demod        : 9
% 1.91/1.20  #Tautology    : 20
% 1.91/1.20  #SimpNegUnit  : 2
% 1.91/1.20  #BackRed      : 0
% 1.91/1.20  
% 1.91/1.20  #Partial instantiations: 0
% 1.91/1.20  #Strategies tried      : 1
% 1.91/1.20  
% 1.91/1.20  Timing (in seconds)
% 1.91/1.20  ----------------------
% 1.91/1.20  Preprocessing        : 0.29
% 1.91/1.20  Parsing              : 0.14
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.15
% 1.91/1.20  Inferencing          : 0.05
% 1.91/1.20  Reduction            : 0.05
% 1.91/1.20  Demodulation         : 0.04
% 1.91/1.20  BG Simplification    : 0.02
% 1.91/1.20  Subsumption          : 0.03
% 1.91/1.20  Abstraction          : 0.01
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.47
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.20  Index Deletion       : 0.00
% 1.91/1.20  Index Matching       : 0.00
% 1.91/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
