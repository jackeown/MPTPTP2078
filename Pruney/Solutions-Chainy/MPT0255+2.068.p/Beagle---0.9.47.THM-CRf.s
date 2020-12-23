%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:48 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 134 expanded)
%              Number of leaves         :   26 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 ( 184 expanded)
%              Number of equality atoms :   14 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( ~ v1_xboole_0(k2_xboole_0(B_9,A_8))
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_54,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_50])).

tff(c_56,plain,(
    ! [B_33,A_34] :
      ( ~ v1_xboole_0(B_33)
      | B_33 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_63,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54,c_63])).

tff(c_74,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_42])).

tff(c_89,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [B_38,A_39] :
      ( ~ v1_xboole_0(k2_xboole_0(B_38,A_39))
      | v1_xboole_0(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_12])).

tff(c_147,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_104])).

tff(c_166,plain,(
    v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_147])).

tff(c_61,plain,(
    ! [A_34] :
      ( A_34 = '#skF_6'
      | ~ v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_54,c_56])).

tff(c_175,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_166,c_61])).

tff(c_22,plain,(
    ! [D_18,B_14] : r2_hidden(D_18,k2_tarski(D_18,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_201,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_22])).

tff(c_14,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,(
    ! [A_10] : r1_xboole_0(A_10,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_14])).

tff(c_249,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,B_51)
      | ~ r2_hidden(C_52,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_253,plain,(
    ! [C_53,A_54] :
      ( ~ r2_hidden(C_53,'#skF_6')
      | ~ r2_hidden(C_53,A_54) ) ),
    inference(resolution,[status(thm)],[c_75,c_249])).

tff(c_267,plain,(
    ! [A_54] : ~ r2_hidden('#skF_4',A_54) ),
    inference(resolution,[status(thm)],[c_201,c_253])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:05:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.21  
% 1.91/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.22  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.91/1.22  
% 1.91/1.22  %Foreground sorts:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Background operators:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Foreground operators:
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.91/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.91/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.22  
% 1.91/1.22  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.91/1.22  tff(f_81, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.91/1.22  tff(f_52, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 1.91/1.22  tff(f_62, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.91/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.91/1.22  tff(f_71, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.91/1.22  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.91/1.22  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.91/1.22  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.91/1.22  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.91/1.22  tff(c_12, plain, (![B_9, A_8]: (~v1_xboole_0(k2_xboole_0(B_9, A_8)) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.22  tff(c_50, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_42, c_12])).
% 1.91/1.22  tff(c_54, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_50])).
% 1.91/1.22  tff(c_56, plain, (![B_33, A_34]: (~v1_xboole_0(B_33) | B_33=A_34 | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.22  tff(c_63, plain, (![A_35]: (k1_xboole_0=A_35 | ~v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_4, c_56])).
% 1.91/1.22  tff(c_70, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_54, c_63])).
% 1.91/1.22  tff(c_74, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_42])).
% 1.91/1.22  tff(c_89, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.22  tff(c_104, plain, (![B_38, A_39]: (~v1_xboole_0(k2_xboole_0(B_38, A_39)) | v1_xboole_0(B_38))), inference(superposition, [status(thm), theory('equality')], [c_89, c_12])).
% 1.91/1.22  tff(c_147, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_104])).
% 1.91/1.22  tff(c_166, plain, (v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_147])).
% 1.91/1.22  tff(c_61, plain, (![A_34]: (A_34='#skF_6' | ~v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_54, c_56])).
% 1.91/1.22  tff(c_175, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_166, c_61])).
% 1.91/1.22  tff(c_22, plain, (![D_18, B_14]: (r2_hidden(D_18, k2_tarski(D_18, B_14)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.91/1.22  tff(c_201, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_175, c_22])).
% 1.91/1.22  tff(c_14, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.91/1.22  tff(c_75, plain, (![A_10]: (r1_xboole_0(A_10, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_14])).
% 1.91/1.22  tff(c_249, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, B_51) | ~r2_hidden(C_52, A_50))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.22  tff(c_253, plain, (![C_53, A_54]: (~r2_hidden(C_53, '#skF_6') | ~r2_hidden(C_53, A_54))), inference(resolution, [status(thm)], [c_75, c_249])).
% 1.91/1.22  tff(c_267, plain, (![A_54]: (~r2_hidden('#skF_4', A_54))), inference(resolution, [status(thm)], [c_201, c_253])).
% 1.91/1.22  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_267, c_201])).
% 1.91/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  Inference rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Ref     : 0
% 1.91/1.22  #Sup     : 58
% 1.91/1.22  #Fact    : 0
% 1.91/1.22  #Define  : 0
% 1.91/1.22  #Split   : 1
% 1.91/1.23  #Chain   : 0
% 1.91/1.23  #Close   : 0
% 1.91/1.23  
% 1.91/1.23  Ordering : KBO
% 1.91/1.23  
% 1.91/1.23  Simplification rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Subsume      : 6
% 1.91/1.23  #Demod        : 30
% 1.91/1.23  #Tautology    : 40
% 1.91/1.23  #SimpNegUnit  : 1
% 1.91/1.23  #BackRed      : 8
% 1.91/1.23  
% 1.91/1.23  #Partial instantiations: 0
% 1.91/1.23  #Strategies tried      : 1
% 1.91/1.23  
% 1.91/1.23  Timing (in seconds)
% 1.91/1.23  ----------------------
% 2.10/1.23  Preprocessing        : 0.30
% 2.10/1.23  Parsing              : 0.15
% 2.10/1.23  CNF conversion       : 0.02
% 2.10/1.23  Main loop            : 0.17
% 2.10/1.23  Inferencing          : 0.05
% 2.10/1.23  Reduction            : 0.06
% 2.10/1.23  Demodulation         : 0.05
% 2.10/1.23  BG Simplification    : 0.01
% 2.10/1.23  Subsumption          : 0.03
% 2.10/1.23  Abstraction          : 0.01
% 2.10/1.23  MUC search           : 0.00
% 2.10/1.23  Cooper               : 0.00
% 2.10/1.23  Total                : 0.49
% 2.10/1.23  Index Insertion      : 0.00
% 2.10/1.23  Index Deletion       : 0.00
% 2.10/1.23  Index Matching       : 0.00
% 2.10/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
