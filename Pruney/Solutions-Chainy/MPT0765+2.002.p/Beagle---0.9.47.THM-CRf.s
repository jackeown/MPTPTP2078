%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:36 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   37 (  48 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 ( 124 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_wellord1 > r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ~ ( v2_wellord1(A)
            & k3_relat_1(A) != k1_xboole_0
            & ! [B] :
                ~ ( r2_hidden(B,k3_relat_1(A))
                  & ! [C] :
                      ( r2_hidden(C,k3_relat_1(A))
                     => r2_hidden(k4_tarski(B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( r2_wellord1(A,k3_relat_1(A))
      <=> v2_wellord1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_wellord1(B,A)
       => ! [C] :
            ~ ( r1_tarski(C,A)
              & C != k1_xboole_0
              & ! [D] :
                  ~ ( r2_hidden(D,C)
                    & ! [E] :
                        ( r2_hidden(E,C)
                       => r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_3] :
      ( r2_wellord1(A_3,k3_relat_1(A_3))
      | ~ v2_wellord1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    k3_relat_1('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_4,B_5,C_13] :
      ( r2_hidden('#skF_1'(A_4,B_5,C_13),C_13)
      | k1_xboole_0 = C_13
      | ~ r1_tarski(C_13,A_4)
      | ~ r2_wellord1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [B_22] :
      ( r2_hidden('#skF_3'(B_22),k3_relat_1('#skF_2'))
      | ~ r2_hidden(B_22,k3_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_43,plain,(
    ! [A_34,B_35,C_36,E_37] :
      ( r2_hidden(k4_tarski('#skF_1'(A_34,B_35,C_36),E_37),B_35)
      | ~ r2_hidden(E_37,C_36)
      | k1_xboole_0 = C_36
      | ~ r1_tarski(C_36,A_34)
      | ~ r2_wellord1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [B_22] :
      ( ~ r2_hidden(k4_tarski(B_22,'#skF_3'(B_22)),'#skF_2')
      | ~ r2_hidden(B_22,k3_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_47,plain,(
    ! [A_34,C_36] :
      ( ~ r2_hidden('#skF_1'(A_34,'#skF_2',C_36),k3_relat_1('#skF_2'))
      | ~ r2_hidden('#skF_3'('#skF_1'(A_34,'#skF_2',C_36)),C_36)
      | k1_xboole_0 = C_36
      | ~ r1_tarski(C_36,A_34)
      | ~ r2_wellord1('#skF_2',A_34)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_43,c_22])).

tff(c_51,plain,(
    ! [A_38,C_39] :
      ( ~ r2_hidden('#skF_1'(A_38,'#skF_2',C_39),k3_relat_1('#skF_2'))
      | ~ r2_hidden('#skF_3'('#skF_1'(A_38,'#skF_2',C_39)),C_39)
      | k1_xboole_0 = C_39
      | ~ r1_tarski(C_39,A_38)
      | ~ r2_wellord1('#skF_2',A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_47])).

tff(c_55,plain,(
    ! [A_38] :
      ( k3_relat_1('#skF_2') = k1_xboole_0
      | ~ r1_tarski(k3_relat_1('#skF_2'),A_38)
      | ~ r2_wellord1('#skF_2',A_38)
      | ~ r2_hidden('#skF_1'(A_38,'#skF_2',k3_relat_1('#skF_2')),k3_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_24,c_51])).

tff(c_59,plain,(
    ! [A_40] :
      ( ~ r1_tarski(k3_relat_1('#skF_2'),A_40)
      | ~ r2_wellord1('#skF_2',A_40)
      | ~ r2_hidden('#skF_1'(A_40,'#skF_2',k3_relat_1('#skF_2')),k3_relat_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_55])).

tff(c_63,plain,(
    ! [A_4] :
      ( k3_relat_1('#skF_2') = k1_xboole_0
      | ~ r1_tarski(k3_relat_1('#skF_2'),A_4)
      | ~ r2_wellord1('#skF_2',A_4)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_59])).

tff(c_66,plain,(
    ! [A_4] :
      ( k3_relat_1('#skF_2') = k1_xboole_0
      | ~ r1_tarski(k3_relat_1('#skF_2'),A_4)
      | ~ r2_wellord1('#skF_2',A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_63])).

tff(c_68,plain,(
    ! [A_41] :
      ( ~ r1_tarski(k3_relat_1('#skF_2'),A_41)
      | ~ r2_wellord1('#skF_2',A_41) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_66])).

tff(c_73,plain,(
    ~ r2_wellord1('#skF_2',k3_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_76,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_73])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:55:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.18  %$ r2_wellord1 > r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.68/1.18  
% 1.68/1.18  %Foreground sorts:
% 1.68/1.18  
% 1.68/1.18  
% 1.68/1.18  %Background operators:
% 1.68/1.18  
% 1.68/1.18  
% 1.68/1.18  %Foreground operators:
% 1.68/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.68/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.18  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.68/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.18  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 1.68/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.18  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.18  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.18  
% 1.77/1.19  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => ~((v2_wellord1(A) & ~(k3_relat_1(A) = k1_xboole_0)) & (![B]: ~(r2_hidden(B, k3_relat_1(A)) & (![C]: (r2_hidden(C, k3_relat_1(A)) => r2_hidden(k4_tarski(B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord1)).
% 1.77/1.19  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (r2_wellord1(A, k3_relat_1(A)) <=> v2_wellord1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord1)).
% 1.77/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.77/1.19  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r2_wellord1(B, A) => (![C]: ~((r1_tarski(C, A) & ~(C = k1_xboole_0)) & (![D]: ~(r2_hidden(D, C) & (![E]: (r2_hidden(E, C) => r2_hidden(k4_tarski(D, E), B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_wellord1)).
% 1.77/1.19  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.77/1.19  tff(c_18, plain, (v2_wellord1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.77/1.19  tff(c_8, plain, (![A_3]: (r2_wellord1(A_3, k3_relat_1(A_3)) | ~v2_wellord1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.77/1.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.19  tff(c_16, plain, (k3_relat_1('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.77/1.19  tff(c_14, plain, (![A_4, B_5, C_13]: (r2_hidden('#skF_1'(A_4, B_5, C_13), C_13) | k1_xboole_0=C_13 | ~r1_tarski(C_13, A_4) | ~r2_wellord1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.77/1.19  tff(c_24, plain, (![B_22]: (r2_hidden('#skF_3'(B_22), k3_relat_1('#skF_2')) | ~r2_hidden(B_22, k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.77/1.19  tff(c_43, plain, (![A_34, B_35, C_36, E_37]: (r2_hidden(k4_tarski('#skF_1'(A_34, B_35, C_36), E_37), B_35) | ~r2_hidden(E_37, C_36) | k1_xboole_0=C_36 | ~r1_tarski(C_36, A_34) | ~r2_wellord1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.77/1.19  tff(c_22, plain, (![B_22]: (~r2_hidden(k4_tarski(B_22, '#skF_3'(B_22)), '#skF_2') | ~r2_hidden(B_22, k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.77/1.19  tff(c_47, plain, (![A_34, C_36]: (~r2_hidden('#skF_1'(A_34, '#skF_2', C_36), k3_relat_1('#skF_2')) | ~r2_hidden('#skF_3'('#skF_1'(A_34, '#skF_2', C_36)), C_36) | k1_xboole_0=C_36 | ~r1_tarski(C_36, A_34) | ~r2_wellord1('#skF_2', A_34) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_43, c_22])).
% 1.77/1.19  tff(c_51, plain, (![A_38, C_39]: (~r2_hidden('#skF_1'(A_38, '#skF_2', C_39), k3_relat_1('#skF_2')) | ~r2_hidden('#skF_3'('#skF_1'(A_38, '#skF_2', C_39)), C_39) | k1_xboole_0=C_39 | ~r1_tarski(C_39, A_38) | ~r2_wellord1('#skF_2', A_38))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_47])).
% 1.77/1.19  tff(c_55, plain, (![A_38]: (k3_relat_1('#skF_2')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_2'), A_38) | ~r2_wellord1('#skF_2', A_38) | ~r2_hidden('#skF_1'(A_38, '#skF_2', k3_relat_1('#skF_2')), k3_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_24, c_51])).
% 1.77/1.19  tff(c_59, plain, (![A_40]: (~r1_tarski(k3_relat_1('#skF_2'), A_40) | ~r2_wellord1('#skF_2', A_40) | ~r2_hidden('#skF_1'(A_40, '#skF_2', k3_relat_1('#skF_2')), k3_relat_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_16, c_55])).
% 1.77/1.19  tff(c_63, plain, (![A_4]: (k3_relat_1('#skF_2')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_2'), A_4) | ~r2_wellord1('#skF_2', A_4) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_59])).
% 1.77/1.19  tff(c_66, plain, (![A_4]: (k3_relat_1('#skF_2')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_2'), A_4) | ~r2_wellord1('#skF_2', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_63])).
% 1.77/1.19  tff(c_68, plain, (![A_41]: (~r1_tarski(k3_relat_1('#skF_2'), A_41) | ~r2_wellord1('#skF_2', A_41))), inference(negUnitSimplification, [status(thm)], [c_16, c_66])).
% 1.77/1.19  tff(c_73, plain, (~r2_wellord1('#skF_2', k3_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_68])).
% 1.77/1.19  tff(c_76, plain, (~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_73])).
% 1.77/1.19  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_76])).
% 1.77/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.19  
% 1.77/1.19  Inference rules
% 1.77/1.19  ----------------------
% 1.77/1.19  #Ref     : 0
% 1.77/1.19  #Sup     : 7
% 1.77/1.19  #Fact    : 0
% 1.77/1.19  #Define  : 0
% 1.77/1.19  #Split   : 0
% 1.77/1.19  #Chain   : 0
% 1.77/1.19  #Close   : 0
% 1.77/1.19  
% 1.77/1.19  Ordering : KBO
% 1.77/1.19  
% 1.77/1.19  Simplification rules
% 1.77/1.19  ----------------------
% 1.77/1.19  #Subsume      : 1
% 1.77/1.19  #Demod        : 6
% 1.77/1.19  #Tautology    : 3
% 1.77/1.19  #SimpNegUnit  : 2
% 1.77/1.19  #BackRed      : 0
% 1.77/1.19  
% 1.77/1.19  #Partial instantiations: 0
% 1.77/1.19  #Strategies tried      : 1
% 1.77/1.19  
% 1.77/1.19  Timing (in seconds)
% 1.77/1.19  ----------------------
% 1.77/1.19  Preprocessing        : 0.27
% 1.77/1.19  Parsing              : 0.15
% 1.77/1.19  CNF conversion       : 0.02
% 1.77/1.19  Main loop            : 0.11
% 1.77/1.19  Inferencing          : 0.05
% 1.77/1.19  Reduction            : 0.03
% 1.77/1.19  Demodulation         : 0.02
% 1.77/1.19  BG Simplification    : 0.01
% 1.77/1.19  Subsumption          : 0.02
% 1.77/1.19  Abstraction          : 0.00
% 1.77/1.19  MUC search           : 0.00
% 1.77/1.19  Cooper               : 0.00
% 1.77/1.19  Total                : 0.40
% 1.77/1.19  Index Insertion      : 0.00
% 1.77/1.19  Index Deletion       : 0.00
% 1.77/1.19  Index Matching       : 0.00
% 1.77/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
