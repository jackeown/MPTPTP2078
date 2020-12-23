%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:27 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   41 (  56 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   53 (  97 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_38,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_95,plain,(
    ! [A_31] :
      ( k2_xboole_0(k1_relat_1(A_31),k2_relat_1(A_31)) = k3_relat_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_139,plain,(
    ! [D_37,A_38] :
      ( ~ r2_hidden(D_37,k2_relat_1(A_38))
      | r2_hidden(D_37,k3_relat_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_4])).

tff(c_28,plain,(
    r2_hidden(k4_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ! [A_20,C_21,B_22] :
      ( r2_hidden(A_20,k1_relat_1(C_21))
      | ~ r2_hidden(k4_tarski(A_20,B_22),C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_56])).

tff(c_77,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_71])).

tff(c_34,plain,(
    ! [A_17] :
      ( k2_xboole_0(k1_relat_1(A_17),k2_relat_1(A_17)) = k3_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    ! [D_23,A_24] :
      ( ~ r2_hidden(D_23,k1_relat_1(A_24))
      | r2_hidden(D_23,k3_relat_1(A_24))
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_26,plain,
    ( ~ r2_hidden('#skF_4',k3_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_31,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_85,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_31])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_77,c_85])).

tff(c_91,plain,(
    ~ r2_hidden('#skF_4',k3_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_146,plain,
    ( ~ r2_hidden('#skF_4',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_139,c_91])).

tff(c_150,plain,(
    ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_146])).

tff(c_151,plain,(
    ! [B_39,C_40,A_41] :
      ( r2_hidden(B_39,k2_relat_1(C_40))
      | ~ r2_hidden(k4_tarski(A_41,B_39),C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_170,plain,
    ( r2_hidden('#skF_4',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_151])).

tff(c_177,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_170])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.17  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.85/1.17  
% 1.85/1.17  %Foreground sorts:
% 1.85/1.17  
% 1.85/1.17  
% 1.85/1.17  %Background operators:
% 1.85/1.17  
% 1.85/1.17  
% 1.85/1.17  %Foreground operators:
% 1.85/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.85/1.17  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.85/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.85/1.17  
% 1.85/1.18  tff(f_55, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 1.85/1.18  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.85/1.18  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.85/1.18  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 1.85/1.18  tff(c_30, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.85/1.18  tff(c_95, plain, (![A_31]: (k2_xboole_0(k1_relat_1(A_31), k2_relat_1(A_31))=k3_relat_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.18  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.18  tff(c_139, plain, (![D_37, A_38]: (~r2_hidden(D_37, k2_relat_1(A_38)) | r2_hidden(D_37, k3_relat_1(A_38)) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_95, c_4])).
% 1.85/1.18  tff(c_28, plain, (r2_hidden(k4_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.85/1.18  tff(c_56, plain, (![A_20, C_21, B_22]: (r2_hidden(A_20, k1_relat_1(C_21)) | ~r2_hidden(k4_tarski(A_20, B_22), C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.18  tff(c_71, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_56])).
% 1.85/1.18  tff(c_77, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_71])).
% 1.85/1.18  tff(c_34, plain, (![A_17]: (k2_xboole_0(k1_relat_1(A_17), k2_relat_1(A_17))=k3_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.18  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.18  tff(c_78, plain, (![D_23, A_24]: (~r2_hidden(D_23, k1_relat_1(A_24)) | r2_hidden(D_23, k3_relat_1(A_24)) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_34, c_6])).
% 1.85/1.18  tff(c_26, plain, (~r2_hidden('#skF_4', k3_relat_1('#skF_5')) | ~r2_hidden('#skF_3', k3_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.85/1.18  tff(c_31, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_26])).
% 1.85/1.18  tff(c_85, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_31])).
% 1.85/1.18  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_77, c_85])).
% 1.85/1.18  tff(c_91, plain, (~r2_hidden('#skF_4', k3_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_26])).
% 1.85/1.18  tff(c_146, plain, (~r2_hidden('#skF_4', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_139, c_91])).
% 1.85/1.18  tff(c_150, plain, (~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_146])).
% 1.85/1.18  tff(c_151, plain, (![B_39, C_40, A_41]: (r2_hidden(B_39, k2_relat_1(C_40)) | ~r2_hidden(k4_tarski(A_41, B_39), C_40) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.18  tff(c_170, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_151])).
% 1.85/1.18  tff(c_177, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_170])).
% 1.85/1.18  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_177])).
% 1.85/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.18  
% 1.85/1.18  Inference rules
% 1.85/1.18  ----------------------
% 1.85/1.18  #Ref     : 0
% 1.85/1.18  #Sup     : 27
% 1.85/1.18  #Fact    : 0
% 1.85/1.18  #Define  : 0
% 1.85/1.18  #Split   : 1
% 1.85/1.18  #Chain   : 0
% 1.85/1.18  #Close   : 0
% 1.85/1.18  
% 1.85/1.18  Ordering : KBO
% 1.85/1.18  
% 1.85/1.18  Simplification rules
% 1.85/1.18  ----------------------
% 1.85/1.18  #Subsume      : 0
% 1.85/1.18  #Demod        : 8
% 1.85/1.18  #Tautology    : 4
% 1.85/1.18  #SimpNegUnit  : 1
% 1.85/1.18  #BackRed      : 0
% 1.85/1.18  
% 1.85/1.18  #Partial instantiations: 0
% 1.85/1.18  #Strategies tried      : 1
% 1.85/1.18  
% 1.85/1.18  Timing (in seconds)
% 1.85/1.18  ----------------------
% 1.85/1.18  Preprocessing        : 0.27
% 1.85/1.18  Parsing              : 0.15
% 1.85/1.18  CNF conversion       : 0.02
% 1.85/1.18  Main loop            : 0.16
% 1.85/1.18  Inferencing          : 0.06
% 1.85/1.18  Reduction            : 0.04
% 1.85/1.18  Demodulation         : 0.03
% 1.85/1.18  BG Simplification    : 0.01
% 1.85/1.18  Subsumption          : 0.03
% 1.85/1.19  Abstraction          : 0.01
% 1.85/1.19  MUC search           : 0.00
% 1.85/1.19  Cooper               : 0.00
% 1.85/1.19  Total                : 0.45
% 1.85/1.19  Index Insertion      : 0.00
% 1.85/1.19  Index Deletion       : 0.00
% 1.85/1.19  Index Matching       : 0.00
% 1.85/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
