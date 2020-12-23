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
% DateTime   : Thu Dec  3 10:01:52 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  53 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(k2_xboole_0(A_28,C_29),B_30)
      | ~ r1_tarski(C_29,B_30)
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [B_20,A_21] :
      ( B_20 = A_21
      | ~ r1_tarski(B_20,A_21)
      | ~ r1_tarski(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),A_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_123,plain,(
    ! [B_30,C_29] :
      ( k2_xboole_0(B_30,C_29) = B_30
      | ~ r1_tarski(C_29,B_30)
      | ~ r1_tarski(B_30,B_30) ) ),
    inference(resolution,[status(thm)],[c_111,c_83])).

tff(c_142,plain,(
    ! [B_31,C_32] :
      ( k2_xboole_0(B_31,C_32) = B_31
      | ~ r1_tarski(C_32,B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_123])).

tff(c_162,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_142])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_216,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_2])).

tff(c_270,plain,(
    ! [C_34,A_35,B_36] :
      ( k2_xboole_0(k10_relat_1(C_34,A_35),k10_relat_1(C_34,B_36)) = k10_relat_1(C_34,k2_xboole_0(A_35,B_36))
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_799,plain,(
    ! [C_49,A_50,B_51] :
      ( r1_tarski(k10_relat_1(C_49,A_50),k10_relat_1(C_49,k2_xboole_0(A_50,B_51)))
      | ~ v1_relat_1(C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_10])).

tff(c_964,plain,(
    ! [C_54] :
      ( r1_tarski(k10_relat_1(C_54,'#skF_1'),k10_relat_1(C_54,'#skF_2'))
      | ~ v1_relat_1(C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_799])).

tff(c_16,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_975,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_964,c_16])).

tff(c_983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:51:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.33  
% 2.28/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.33  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.60/1.33  
% 2.60/1.33  %Foreground sorts:
% 2.60/1.33  
% 2.60/1.33  
% 2.60/1.33  %Background operators:
% 2.60/1.33  
% 2.60/1.33  
% 2.60/1.33  %Foreground operators:
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.60/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.60/1.33  
% 2.60/1.34  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 2.60/1.34  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.60/1.34  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.60/1.34  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.60/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.60/1.34  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 2.60/1.34  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.60/1.34  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.60/1.34  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.34  tff(c_111, plain, (![A_28, C_29, B_30]: (r1_tarski(k2_xboole_0(A_28, C_29), B_30) | ~r1_tarski(C_29, B_30) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.60/1.34  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.34  tff(c_73, plain, (![B_20, A_21]: (B_20=A_21 | ~r1_tarski(B_20, A_21) | ~r1_tarski(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.34  tff(c_83, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(k2_xboole_0(A_5, B_6), A_5))), inference(resolution, [status(thm)], [c_10, c_73])).
% 2.60/1.34  tff(c_123, plain, (![B_30, C_29]: (k2_xboole_0(B_30, C_29)=B_30 | ~r1_tarski(C_29, B_30) | ~r1_tarski(B_30, B_30))), inference(resolution, [status(thm)], [c_111, c_83])).
% 2.60/1.34  tff(c_142, plain, (![B_31, C_32]: (k2_xboole_0(B_31, C_32)=B_31 | ~r1_tarski(C_32, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_123])).
% 2.60/1.34  tff(c_162, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_18, c_142])).
% 2.60/1.34  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.34  tff(c_216, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_162, c_2])).
% 2.60/1.34  tff(c_270, plain, (![C_34, A_35, B_36]: (k2_xboole_0(k10_relat_1(C_34, A_35), k10_relat_1(C_34, B_36))=k10_relat_1(C_34, k2_xboole_0(A_35, B_36)) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.34  tff(c_799, plain, (![C_49, A_50, B_51]: (r1_tarski(k10_relat_1(C_49, A_50), k10_relat_1(C_49, k2_xboole_0(A_50, B_51))) | ~v1_relat_1(C_49))), inference(superposition, [status(thm), theory('equality')], [c_270, c_10])).
% 2.60/1.34  tff(c_964, plain, (![C_54]: (r1_tarski(k10_relat_1(C_54, '#skF_1'), k10_relat_1(C_54, '#skF_2')) | ~v1_relat_1(C_54))), inference(superposition, [status(thm), theory('equality')], [c_216, c_799])).
% 2.60/1.34  tff(c_16, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.60/1.34  tff(c_975, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_964, c_16])).
% 2.60/1.34  tff(c_983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_975])).
% 2.60/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.34  
% 2.60/1.34  Inference rules
% 2.60/1.34  ----------------------
% 2.60/1.34  #Ref     : 0
% 2.60/1.34  #Sup     : 243
% 2.60/1.34  #Fact    : 0
% 2.60/1.34  #Define  : 0
% 2.60/1.34  #Split   : 1
% 2.60/1.34  #Chain   : 0
% 2.60/1.34  #Close   : 0
% 2.60/1.34  
% 2.60/1.34  Ordering : KBO
% 2.60/1.34  
% 2.60/1.34  Simplification rules
% 2.60/1.34  ----------------------
% 2.60/1.34  #Subsume      : 20
% 2.60/1.34  #Demod        : 206
% 2.60/1.34  #Tautology    : 139
% 2.60/1.34  #SimpNegUnit  : 0
% 2.60/1.34  #BackRed      : 0
% 2.60/1.34  
% 2.60/1.34  #Partial instantiations: 0
% 2.60/1.34  #Strategies tried      : 1
% 2.60/1.34  
% 2.60/1.34  Timing (in seconds)
% 2.60/1.34  ----------------------
% 2.60/1.35  Preprocessing        : 0.26
% 2.60/1.35  Parsing              : 0.14
% 2.60/1.35  CNF conversion       : 0.02
% 2.60/1.35  Main loop            : 0.35
% 2.60/1.35  Inferencing          : 0.12
% 2.60/1.35  Reduction            : 0.14
% 2.60/1.35  Demodulation         : 0.11
% 2.60/1.35  BG Simplification    : 0.01
% 2.60/1.35  Subsumption          : 0.06
% 2.60/1.35  Abstraction          : 0.02
% 2.60/1.35  MUC search           : 0.00
% 2.60/1.35  Cooper               : 0.00
% 2.60/1.35  Total                : 0.64
% 2.60/1.35  Index Insertion      : 0.00
% 2.60/1.35  Index Deletion       : 0.00
% 2.60/1.35  Index Matching       : 0.00
% 2.60/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
