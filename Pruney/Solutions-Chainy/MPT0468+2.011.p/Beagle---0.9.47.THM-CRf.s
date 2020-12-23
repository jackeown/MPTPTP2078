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
% DateTime   : Thu Dec  3 09:58:50 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  65 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_116,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(k4_tarski('#skF_3'(A_75,B_76),'#skF_4'(A_75,B_76)),A_75)
      | r1_tarski(A_75,B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [B_46,C_47] : ~ r2_hidden(k4_tarski(B_46,C_47),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_129,plain,(
    ! [B_76] :
      ( r1_tarski('#skF_9',B_76)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_116,c_30])).

tff(c_135,plain,(
    ! [B_76] : r1_tarski('#skF_9',B_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_129])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,(
    ! [C_56,B_57,A_58] :
      ( r2_hidden(C_56,B_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [A_6,B_57] :
      ( r2_hidden('#skF_2'(A_6),B_57)
      | ~ r1_tarski(A_6,B_57)
      | k1_xboole_0 = A_6 ) ),
    inference(resolution,[status(thm)],[c_8,c_43])).

tff(c_72,plain,(
    ! [C_72,A_73] :
      ( r2_hidden(k4_tarski(C_72,'#skF_8'(A_73,k1_relat_1(A_73),C_72)),A_73)
      | ~ r2_hidden(C_72,k1_relat_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_85,plain,(
    ! [C_74] : ~ r2_hidden(C_74,k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_72,c_30])).

tff(c_115,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_85])).

tff(c_84,plain,(
    ! [C_72] : ~ r2_hidden(C_72,k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_72,c_30])).

tff(c_150,plain,(
    ! [C_78] : ~ r2_hidden(C_78,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_84])).

tff(c_247,plain,(
    ! [A_83] :
      ( ~ r1_tarski(A_83,k1_xboole_0)
      | k1_xboole_0 = A_83 ) ),
    inference(resolution,[status(thm)],[c_49,c_150])).

tff(c_255,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_135,c_247])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:54:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 1.87/1.18  
% 1.87/1.18  %Foreground sorts:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Background operators:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Foreground operators:
% 1.87/1.18  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.87/1.18  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.87/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.87/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.18  tff('#skF_9', type, '#skF_9': $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.18  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 1.87/1.18  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.87/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.18  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.87/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.87/1.18  
% 1.87/1.19  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 1.87/1.19  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 1.87/1.19  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.87/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.87/1.19  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.87/1.19  tff(c_28, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.19  tff(c_32, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.19  tff(c_116, plain, (![A_75, B_76]: (r2_hidden(k4_tarski('#skF_3'(A_75, B_76), '#skF_4'(A_75, B_76)), A_75) | r1_tarski(A_75, B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.19  tff(c_30, plain, (![B_46, C_47]: (~r2_hidden(k4_tarski(B_46, C_47), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.19  tff(c_129, plain, (![B_76]: (r1_tarski('#skF_9', B_76) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_116, c_30])).
% 1.87/1.19  tff(c_135, plain, (![B_76]: (r1_tarski('#skF_9', B_76))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_129])).
% 1.87/1.19  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.87/1.19  tff(c_43, plain, (![C_56, B_57, A_58]: (r2_hidden(C_56, B_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.19  tff(c_49, plain, (![A_6, B_57]: (r2_hidden('#skF_2'(A_6), B_57) | ~r1_tarski(A_6, B_57) | k1_xboole_0=A_6)), inference(resolution, [status(thm)], [c_8, c_43])).
% 1.87/1.19  tff(c_72, plain, (![C_72, A_73]: (r2_hidden(k4_tarski(C_72, '#skF_8'(A_73, k1_relat_1(A_73), C_72)), A_73) | ~r2_hidden(C_72, k1_relat_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.19  tff(c_85, plain, (![C_74]: (~r2_hidden(C_74, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_72, c_30])).
% 1.87/1.19  tff(c_115, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_85])).
% 1.87/1.19  tff(c_84, plain, (![C_72]: (~r2_hidden(C_72, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_72, c_30])).
% 1.87/1.19  tff(c_150, plain, (![C_78]: (~r2_hidden(C_78, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_84])).
% 1.87/1.19  tff(c_247, plain, (![A_83]: (~r1_tarski(A_83, k1_xboole_0) | k1_xboole_0=A_83)), inference(resolution, [status(thm)], [c_49, c_150])).
% 1.87/1.19  tff(c_255, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_135, c_247])).
% 1.87/1.19  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_255])).
% 1.87/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  Inference rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Ref     : 0
% 1.87/1.19  #Sup     : 47
% 1.87/1.19  #Fact    : 0
% 1.87/1.19  #Define  : 0
% 1.87/1.19  #Split   : 0
% 1.87/1.19  #Chain   : 0
% 1.87/1.19  #Close   : 0
% 1.87/1.19  
% 1.87/1.19  Ordering : KBO
% 1.87/1.19  
% 1.87/1.19  Simplification rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Subsume      : 9
% 1.87/1.19  #Demod        : 12
% 1.87/1.19  #Tautology    : 11
% 1.87/1.19  #SimpNegUnit  : 3
% 1.87/1.19  #BackRed      : 2
% 1.87/1.19  
% 1.87/1.19  #Partial instantiations: 0
% 1.87/1.19  #Strategies tried      : 1
% 1.87/1.19  
% 1.87/1.19  Timing (in seconds)
% 1.87/1.19  ----------------------
% 1.87/1.19  Preprocessing        : 0.28
% 1.87/1.19  Parsing              : 0.14
% 1.87/1.19  CNF conversion       : 0.02
% 1.87/1.19  Main loop            : 0.17
% 1.87/1.19  Inferencing          : 0.07
% 1.87/1.19  Reduction            : 0.05
% 1.87/1.19  Demodulation         : 0.03
% 1.87/1.19  BG Simplification    : 0.01
% 1.87/1.19  Subsumption          : 0.03
% 1.87/1.19  Abstraction          : 0.01
% 1.87/1.19  MUC search           : 0.00
% 1.87/1.19  Cooper               : 0.00
% 1.87/1.19  Total                : 0.47
% 1.87/1.19  Index Insertion      : 0.00
% 1.87/1.19  Index Deletion       : 0.00
% 1.87/1.19  Index Matching       : 0.00
% 1.87/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
