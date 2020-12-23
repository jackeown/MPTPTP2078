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
% DateTime   : Thu Dec  3 09:58:50 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   37 (  60 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  98 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_942,plain,(
    ! [A_1015,B_1016] :
      ( r2_hidden(k4_tarski('#skF_5'(A_1015,B_1016),'#skF_6'(A_1015,B_1016)),A_1015)
      | r1_tarski(A_1015,B_1016)
      | ~ v1_relat_1(A_1015) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [B_32,C_33] : ~ r2_hidden(k4_tarski(B_32,C_33),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_958,plain,(
    ! [B_1016] :
      ( r1_tarski('#skF_7',B_1016)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_942,c_30])).

tff(c_973,plain,(
    ! [B_1045] : r1_tarski('#skF_7',B_1045) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_958])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [C_45,B_46,A_47] :
      ( r2_hidden(C_45,B_46)
      | ~ r2_hidden(C_45,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_2'(A_51),B_52)
      | ~ r1_tarski(A_51,B_52)
      | k1_xboole_0 = A_51 ) ),
    inference(resolution,[status(thm)],[c_8,c_73])).

tff(c_10,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [A_8,A_51] :
      ( A_8 = '#skF_2'(A_51)
      | ~ r1_tarski(A_51,k1_tarski(A_8))
      | k1_xboole_0 = A_51 ) ),
    inference(resolution,[status(thm)],[c_91,c_10])).

tff(c_982,plain,(
    ! [A_8] :
      ( A_8 = '#skF_2'('#skF_7')
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_973,c_102])).

tff(c_1002,plain,(
    '#skF_2'('#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_982])).

tff(c_988,plain,(
    ! [A_8] : A_8 = '#skF_2'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_982])).

tff(c_1464,plain,(
    ! [A_2072] : A_2072 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_988])).

tff(c_1534,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1464,c_28])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.54  
% 3.28/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.54  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.28/1.54  
% 3.28/1.54  %Foreground sorts:
% 3.28/1.54  
% 3.28/1.54  
% 3.28/1.54  %Background operators:
% 3.28/1.54  
% 3.28/1.54  
% 3.28/1.54  %Foreground operators:
% 3.28/1.54  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.28/1.54  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.28/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.28/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.28/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.28/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.28/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.28/1.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.28/1.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.28/1.54  
% 3.28/1.55  tff(f_66, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 3.28/1.55  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 3.28/1.55  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.28/1.55  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.28/1.55  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.28/1.55  tff(c_28, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.28/1.55  tff(c_32, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.28/1.55  tff(c_942, plain, (![A_1015, B_1016]: (r2_hidden(k4_tarski('#skF_5'(A_1015, B_1016), '#skF_6'(A_1015, B_1016)), A_1015) | r1_tarski(A_1015, B_1016) | ~v1_relat_1(A_1015))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.28/1.55  tff(c_30, plain, (![B_32, C_33]: (~r2_hidden(k4_tarski(B_32, C_33), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.28/1.55  tff(c_958, plain, (![B_1016]: (r1_tarski('#skF_7', B_1016) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_942, c_30])).
% 3.28/1.55  tff(c_973, plain, (![B_1045]: (r1_tarski('#skF_7', B_1045))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_958])).
% 3.28/1.55  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.28/1.55  tff(c_73, plain, (![C_45, B_46, A_47]: (r2_hidden(C_45, B_46) | ~r2_hidden(C_45, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.28/1.55  tff(c_91, plain, (![A_51, B_52]: (r2_hidden('#skF_2'(A_51), B_52) | ~r1_tarski(A_51, B_52) | k1_xboole_0=A_51)), inference(resolution, [status(thm)], [c_8, c_73])).
% 3.28/1.55  tff(c_10, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.55  tff(c_102, plain, (![A_8, A_51]: (A_8='#skF_2'(A_51) | ~r1_tarski(A_51, k1_tarski(A_8)) | k1_xboole_0=A_51)), inference(resolution, [status(thm)], [c_91, c_10])).
% 3.28/1.55  tff(c_982, plain, (![A_8]: (A_8='#skF_2'('#skF_7') | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_973, c_102])).
% 3.28/1.55  tff(c_1002, plain, ('#skF_2'('#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_28, c_982])).
% 3.28/1.55  tff(c_988, plain, (![A_8]: (A_8='#skF_2'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_28, c_982])).
% 3.28/1.55  tff(c_1464, plain, (![A_2072]: (A_2072='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1002, c_988])).
% 3.28/1.55  tff(c_1534, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1464, c_28])).
% 3.28/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.55  
% 3.28/1.55  Inference rules
% 3.28/1.55  ----------------------
% 3.28/1.55  #Ref     : 0
% 3.28/1.55  #Sup     : 273
% 3.28/1.55  #Fact    : 0
% 3.28/1.55  #Define  : 0
% 3.28/1.55  #Split   : 0
% 3.28/1.55  #Chain   : 0
% 3.28/1.55  #Close   : 0
% 3.28/1.55  
% 3.28/1.55  Ordering : KBO
% 3.28/1.55  
% 3.28/1.55  Simplification rules
% 3.28/1.55  ----------------------
% 3.28/1.55  #Subsume      : 49
% 3.28/1.55  #Demod        : 16
% 3.28/1.55  #Tautology    : 40
% 3.28/1.55  #SimpNegUnit  : 26
% 3.28/1.55  #BackRed      : 0
% 3.28/1.55  
% 3.28/1.55  #Partial instantiations: 1027
% 3.28/1.55  #Strategies tried      : 1
% 3.28/1.55  
% 3.28/1.55  Timing (in seconds)
% 3.28/1.55  ----------------------
% 3.28/1.56  Preprocessing        : 0.30
% 3.28/1.56  Parsing              : 0.15
% 3.28/1.56  CNF conversion       : 0.02
% 3.28/1.56  Main loop            : 0.48
% 3.28/1.56  Inferencing          : 0.25
% 3.28/1.56  Reduction            : 0.10
% 3.28/1.56  Demodulation         : 0.07
% 3.28/1.56  BG Simplification    : 0.03
% 3.28/1.56  Subsumption          : 0.08
% 3.28/1.56  Abstraction          : 0.02
% 3.28/1.56  MUC search           : 0.00
% 3.28/1.56  Cooper               : 0.00
% 3.28/1.56  Total                : 0.81
% 3.28/1.56  Index Insertion      : 0.00
% 3.28/1.56  Index Deletion       : 0.00
% 3.28/1.56  Index Matching       : 0.00
% 3.28/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
