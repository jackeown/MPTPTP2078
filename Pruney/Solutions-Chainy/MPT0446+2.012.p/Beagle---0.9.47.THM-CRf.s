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
% DateTime   : Thu Dec  3 09:58:27 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    4
%              Number of atoms          :   48 (  78 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_13 > #skF_2 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_167,plain,(
    ! [C_70,A_71,D_72] :
      ( r2_hidden(C_70,k2_relat_1(A_71))
      | ~ r2_hidden(k4_tarski(D_72,C_70),A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_181,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_48,c_167])).

tff(c_152,plain,(
    ! [A_69] :
      ( k2_xboole_0(k1_relat_1(A_69),k2_relat_1(A_69)) = k3_relat_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_199,plain,(
    ! [D_75,A_76] :
      ( ~ r2_hidden(D_75,k2_relat_1(A_76))
      | r2_hidden(D_75,k3_relat_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_4])).

tff(c_54,plain,(
    ! [C_52,A_53,D_54] :
      ( r2_hidden(C_52,k1_relat_1(A_53))
      | ~ r2_hidden(k4_tarski(C_52,D_54),A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_48,c_54])).

tff(c_69,plain,(
    ! [A_55] :
      ( k2_xboole_0(k1_relat_1(A_55),k2_relat_1(A_55)) = k3_relat_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_116,plain,(
    ! [D_61,A_62] :
      ( ~ r2_hidden(D_61,k1_relat_1(A_62))
      | r2_hidden(D_61,k3_relat_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_6])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_12',k3_relat_1('#skF_13'))
    | ~ r2_hidden('#skF_11',k3_relat_1('#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_11',k3_relat_1('#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_127,plain,
    ( ~ r2_hidden('#skF_11',k1_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_116,c_52])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_127])).

tff(c_134,plain,(
    ~ r2_hidden('#skF_12',k3_relat_1('#skF_13')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_210,plain,
    ( ~ r2_hidden('#skF_12',k2_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_199,c_134])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_181,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.28  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_13 > #skF_2 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10
% 2.04/1.28  
% 2.04/1.28  %Foreground sorts:
% 2.04/1.28  
% 2.04/1.28  
% 2.04/1.28  %Background operators:
% 2.04/1.28  
% 2.04/1.28  
% 2.04/1.28  %Foreground operators:
% 2.04/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.28  tff('#skF_11', type, '#skF_11': $i).
% 2.04/1.28  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.04/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.04/1.28  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.04/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.04/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.28  tff('#skF_13', type, '#skF_13': $i).
% 2.04/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.04/1.28  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.28  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.04/1.28  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 2.04/1.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.04/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.28  tff('#skF_12', type, '#skF_12': $i).
% 2.04/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.04/1.28  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 2.04/1.28  
% 2.04/1.29  tff(f_63, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 2.04/1.29  tff(f_50, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.04/1.29  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.04/1.29  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.04/1.29  tff(f_42, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.04/1.29  tff(c_50, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.04/1.29  tff(c_48, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_13')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.04/1.29  tff(c_167, plain, (![C_70, A_71, D_72]: (r2_hidden(C_70, k2_relat_1(A_71)) | ~r2_hidden(k4_tarski(D_72, C_70), A_71))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.29  tff(c_181, plain, (r2_hidden('#skF_12', k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_48, c_167])).
% 2.04/1.29  tff(c_152, plain, (![A_69]: (k2_xboole_0(k1_relat_1(A_69), k2_relat_1(A_69))=k3_relat_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.29  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.04/1.29  tff(c_199, plain, (![D_75, A_76]: (~r2_hidden(D_75, k2_relat_1(A_76)) | r2_hidden(D_75, k3_relat_1(A_76)) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_152, c_4])).
% 2.04/1.29  tff(c_54, plain, (![C_52, A_53, D_54]: (r2_hidden(C_52, k1_relat_1(A_53)) | ~r2_hidden(k4_tarski(C_52, D_54), A_53))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.04/1.29  tff(c_68, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_48, c_54])).
% 2.04/1.29  tff(c_69, plain, (![A_55]: (k2_xboole_0(k1_relat_1(A_55), k2_relat_1(A_55))=k3_relat_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.29  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.04/1.29  tff(c_116, plain, (![D_61, A_62]: (~r2_hidden(D_61, k1_relat_1(A_62)) | r2_hidden(D_61, k3_relat_1(A_62)) | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_69, c_6])).
% 2.04/1.29  tff(c_46, plain, (~r2_hidden('#skF_12', k3_relat_1('#skF_13')) | ~r2_hidden('#skF_11', k3_relat_1('#skF_13'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.04/1.29  tff(c_52, plain, (~r2_hidden('#skF_11', k3_relat_1('#skF_13'))), inference(splitLeft, [status(thm)], [c_46])).
% 2.04/1.29  tff(c_127, plain, (~r2_hidden('#skF_11', k1_relat_1('#skF_13')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_116, c_52])).
% 2.04/1.29  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_127])).
% 2.04/1.29  tff(c_134, plain, (~r2_hidden('#skF_12', k3_relat_1('#skF_13'))), inference(splitRight, [status(thm)], [c_46])).
% 2.04/1.29  tff(c_210, plain, (~r2_hidden('#skF_12', k2_relat_1('#skF_13')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_199, c_134])).
% 2.04/1.29  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_181, c_210])).
% 2.04/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.29  
% 2.04/1.29  Inference rules
% 2.04/1.29  ----------------------
% 2.04/1.29  #Ref     : 0
% 2.04/1.29  #Sup     : 32
% 2.04/1.29  #Fact    : 0
% 2.04/1.29  #Define  : 0
% 2.04/1.29  #Split   : 1
% 2.04/1.29  #Chain   : 0
% 2.04/1.29  #Close   : 0
% 2.04/1.29  
% 2.04/1.29  Ordering : KBO
% 2.04/1.29  
% 2.04/1.29  Simplification rules
% 2.04/1.29  ----------------------
% 2.04/1.29  #Subsume      : 0
% 2.04/1.29  #Demod        : 6
% 2.04/1.29  #Tautology    : 4
% 2.04/1.29  #SimpNegUnit  : 0
% 2.04/1.29  #BackRed      : 0
% 2.04/1.29  
% 2.04/1.29  #Partial instantiations: 0
% 2.04/1.29  #Strategies tried      : 1
% 2.04/1.29  
% 2.04/1.29  Timing (in seconds)
% 2.04/1.29  ----------------------
% 2.04/1.29  Preprocessing        : 0.30
% 2.04/1.29  Parsing              : 0.16
% 2.04/1.29  CNF conversion       : 0.03
% 2.04/1.29  Main loop            : 0.17
% 2.04/1.29  Inferencing          : 0.06
% 2.04/1.29  Reduction            : 0.04
% 2.04/1.29  Demodulation         : 0.03
% 2.04/1.29  BG Simplification    : 0.01
% 2.04/1.29  Subsumption          : 0.04
% 2.04/1.29  Abstraction          : 0.01
% 2.04/1.29  MUC search           : 0.00
% 2.04/1.29  Cooper               : 0.00
% 2.04/1.29  Total                : 0.49
% 2.04/1.29  Index Insertion      : 0.00
% 2.04/1.29  Index Deletion       : 0.00
% 2.04/1.29  Index Matching       : 0.00
% 2.04/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
