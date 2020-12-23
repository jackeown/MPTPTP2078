%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:46 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  36 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_34,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).

tff(c_18,plain,(
    ! [D_16,B_12] : r2_hidden(D_16,k2_tarski(D_16,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_42,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    ! [D_16,B_12] : ~ v1_xboole_0(k2_tarski(D_16,B_12)) ),
    inference(resolution,[status(thm)],[c_18,c_42])).

tff(c_8,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_53,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_2'(A_36),A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(A_37)
      | k1_xboole_0 = A_37 ) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_62,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_58])).

tff(c_63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_122,plain,(
    ! [A_40,B_41] :
      ( ~ v1_xboole_0(k2_xboole_0(A_40,B_41))
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_131,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_122])).

tff(c_133,plain,(
    v1_xboole_0(k2_tarski('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_131])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:29:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.14  
% 1.68/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.15  %$ r2_hidden > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3
% 1.68/1.15  
% 1.68/1.15  %Foreground sorts:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Background operators:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Foreground operators:
% 1.68/1.15  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.68/1.15  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.68/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.68/1.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.68/1.15  tff('#skF_7', type, '#skF_7': $i).
% 1.68/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.68/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.68/1.15  tff('#skF_6', type, '#skF_6': $i).
% 1.68/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.68/1.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.15  
% 1.68/1.15  tff(f_57, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.68/1.15  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.68/1.15  tff(f_34, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 1.68/1.15  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.68/1.15  tff(f_69, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.68/1.15  tff(f_48, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_xboole_0)).
% 1.68/1.15  tff(c_18, plain, (![D_16, B_12]: (r2_hidden(D_16, k2_tarski(D_16, B_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.68/1.15  tff(c_42, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.15  tff(c_46, plain, (![D_16, B_12]: (~v1_xboole_0(k2_tarski(D_16, B_12)))), inference(resolution, [status(thm)], [c_18, c_42])).
% 1.68/1.15  tff(c_8, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.68/1.15  tff(c_53, plain, (![A_36]: (r2_hidden('#skF_2'(A_36), A_36) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.68/1.15  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.15  tff(c_58, plain, (![A_37]: (~v1_xboole_0(A_37) | k1_xboole_0=A_37)), inference(resolution, [status(thm)], [c_53, c_4])).
% 1.68/1.15  tff(c_62, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_58])).
% 1.68/1.15  tff(c_63, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8])).
% 1.68/1.15  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.68/1.15  tff(c_122, plain, (![A_40, B_41]: (~v1_xboole_0(k2_xboole_0(A_40, B_41)) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.68/1.15  tff(c_131, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_122])).
% 1.68/1.15  tff(c_133, plain, (v1_xboole_0(k2_tarski('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_131])).
% 1.68/1.15  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_133])).
% 1.68/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.15  
% 1.68/1.15  Inference rules
% 1.68/1.15  ----------------------
% 1.68/1.15  #Ref     : 0
% 1.68/1.15  #Sup     : 24
% 1.68/1.15  #Fact    : 0
% 1.68/1.15  #Define  : 0
% 1.68/1.15  #Split   : 0
% 1.68/1.15  #Chain   : 0
% 1.68/1.15  #Close   : 0
% 1.68/1.15  
% 1.68/1.15  Ordering : KBO
% 1.68/1.15  
% 1.68/1.15  Simplification rules
% 1.68/1.15  ----------------------
% 1.68/1.15  #Subsume      : 1
% 1.68/1.15  #Demod        : 2
% 1.68/1.15  #Tautology    : 13
% 1.68/1.15  #SimpNegUnit  : 1
% 1.68/1.15  #BackRed      : 1
% 1.68/1.15  
% 1.68/1.15  #Partial instantiations: 0
% 1.68/1.15  #Strategies tried      : 1
% 1.68/1.15  
% 1.68/1.15  Timing (in seconds)
% 1.68/1.15  ----------------------
% 1.68/1.16  Preprocessing        : 0.30
% 1.68/1.16  Parsing              : 0.15
% 1.68/1.16  CNF conversion       : 0.02
% 1.68/1.16  Main loop            : 0.11
% 1.68/1.16  Inferencing          : 0.03
% 1.68/1.16  Reduction            : 0.04
% 1.68/1.16  Demodulation         : 0.03
% 1.68/1.16  BG Simplification    : 0.01
% 1.68/1.16  Subsumption          : 0.02
% 1.68/1.16  Abstraction          : 0.01
% 1.68/1.16  MUC search           : 0.00
% 1.68/1.16  Cooper               : 0.00
% 1.68/1.16  Total                : 0.43
% 1.68/1.16  Index Insertion      : 0.00
% 1.68/1.16  Index Deletion       : 0.00
% 1.68/1.16  Index Matching       : 0.00
% 1.68/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
