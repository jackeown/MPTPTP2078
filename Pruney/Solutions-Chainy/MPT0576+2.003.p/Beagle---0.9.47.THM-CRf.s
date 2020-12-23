%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:54 EST 2020

% Result     : Theorem 17.88s
% Output     : CNFRefutation 17.89s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  74 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k10_relat_1(C,A),k10_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t180_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    ! [B_21,A_20,C_23] :
      ( r1_tarski(k10_relat_1(B_21,A_20),k10_relat_1(C_23,A_20))
      | ~ r1_tarski(B_21,C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_80,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_16,plain,(
    ! [C_19,A_17,B_18] :
      ( k2_xboole_0(k10_relat_1(C_19,A_17),k10_relat_1(C_19,B_18)) = k10_relat_1(C_19,k2_xboole_0(A_17,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_139,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,k2_xboole_0(C_36,B_37))
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_602,plain,(
    ! [A_52,A_53,B_54] :
      ( r1_tarski(A_52,k2_xboole_0(A_53,B_54))
      | ~ r1_tarski(A_52,A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_139])).

tff(c_21551,plain,(
    ! [A_301,C_302,A_303,B_304] :
      ( r1_tarski(A_301,k10_relat_1(C_302,k2_xboole_0(A_303,B_304)))
      | ~ r1_tarski(A_301,k10_relat_1(C_302,A_303))
      | ~ v1_relat_1(C_302) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_602])).

tff(c_69198,plain,(
    ! [A_664,C_665] :
      ( r1_tarski(A_664,k10_relat_1(C_665,'#skF_2'))
      | ~ r1_tarski(A_664,k10_relat_1(C_665,'#skF_1'))
      | ~ v1_relat_1(C_665) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_21551])).

tff(c_20,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_69268,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_69198,c_20])).

tff(c_69294,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_69268])).

tff(c_69297,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_69294])).

tff(c_69301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_69297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.88/9.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.89/9.56  
% 17.89/9.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.89/9.56  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 17.89/9.56  
% 17.89/9.56  %Foreground sorts:
% 17.89/9.56  
% 17.89/9.56  
% 17.89/9.56  %Background operators:
% 17.89/9.56  
% 17.89/9.56  
% 17.89/9.56  %Foreground operators:
% 17.89/9.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.89/9.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.89/9.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.89/9.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.89/9.56  tff('#skF_2', type, '#skF_2': $i).
% 17.89/9.56  tff('#skF_3', type, '#skF_3': $i).
% 17.89/9.56  tff('#skF_1', type, '#skF_1': $i).
% 17.89/9.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.89/9.56  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 17.89/9.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.89/9.56  tff('#skF_4', type, '#skF_4': $i).
% 17.89/9.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.89/9.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.89/9.56  
% 17.89/9.57  tff(f_72, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k10_relat_1(C, A), k10_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t180_relat_1)).
% 17.89/9.57  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t179_relat_1)).
% 17.89/9.57  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 17.89/9.57  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 17.89/9.57  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 17.89/9.57  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 17.89/9.57  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.89/9.57  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.89/9.57  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.89/9.57  tff(c_18, plain, (![B_21, A_20, C_23]: (r1_tarski(k10_relat_1(B_21, A_20), k10_relat_1(C_23, A_20)) | ~r1_tarski(B_21, C_23) | ~v1_relat_1(C_23) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.89/9.57  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.89/9.57  tff(c_80, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.89/9.57  tff(c_96, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_80])).
% 17.89/9.57  tff(c_16, plain, (![C_19, A_17, B_18]: (k2_xboole_0(k10_relat_1(C_19, A_17), k10_relat_1(C_19, B_18))=k10_relat_1(C_19, k2_xboole_0(A_17, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.89/9.57  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.89/9.57  tff(c_139, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, k2_xboole_0(C_36, B_37)) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.89/9.57  tff(c_602, plain, (![A_52, A_53, B_54]: (r1_tarski(A_52, k2_xboole_0(A_53, B_54)) | ~r1_tarski(A_52, A_53))), inference(superposition, [status(thm), theory('equality')], [c_2, c_139])).
% 17.89/9.57  tff(c_21551, plain, (![A_301, C_302, A_303, B_304]: (r1_tarski(A_301, k10_relat_1(C_302, k2_xboole_0(A_303, B_304))) | ~r1_tarski(A_301, k10_relat_1(C_302, A_303)) | ~v1_relat_1(C_302))), inference(superposition, [status(thm), theory('equality')], [c_16, c_602])).
% 17.89/9.57  tff(c_69198, plain, (![A_664, C_665]: (r1_tarski(A_664, k10_relat_1(C_665, '#skF_2')) | ~r1_tarski(A_664, k10_relat_1(C_665, '#skF_1')) | ~v1_relat_1(C_665))), inference(superposition, [status(thm), theory('equality')], [c_96, c_21551])).
% 17.89/9.57  tff(c_20, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.89/9.57  tff(c_69268, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_1')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_69198, c_20])).
% 17.89/9.57  tff(c_69294, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_69268])).
% 17.89/9.57  tff(c_69297, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_69294])).
% 17.89/9.57  tff(c_69301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_69297])).
% 17.89/9.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.89/9.57  
% 17.89/9.57  Inference rules
% 17.89/9.57  ----------------------
% 17.89/9.57  #Ref     : 0
% 17.89/9.57  #Sup     : 17454
% 17.89/9.57  #Fact    : 0
% 17.89/9.57  #Define  : 0
% 17.89/9.57  #Split   : 17
% 17.89/9.57  #Chain   : 0
% 17.89/9.57  #Close   : 0
% 17.89/9.57  
% 17.89/9.57  Ordering : KBO
% 17.89/9.57  
% 17.89/9.57  Simplification rules
% 17.89/9.57  ----------------------
% 17.89/9.57  #Subsume      : 3592
% 17.89/9.57  #Demod        : 14268
% 17.89/9.57  #Tautology    : 8508
% 17.89/9.57  #SimpNegUnit  : 0
% 17.89/9.57  #BackRed      : 32
% 17.89/9.57  
% 17.89/9.57  #Partial instantiations: 0
% 17.89/9.57  #Strategies tried      : 1
% 17.89/9.57  
% 17.89/9.57  Timing (in seconds)
% 17.89/9.57  ----------------------
% 17.89/9.57  Preprocessing        : 0.32
% 17.89/9.57  Parsing              : 0.19
% 17.89/9.57  CNF conversion       : 0.02
% 17.89/9.57  Main loop            : 8.45
% 17.89/9.57  Inferencing          : 1.31
% 17.89/9.57  Reduction            : 4.46
% 17.89/9.57  Demodulation         : 3.95
% 17.89/9.57  BG Simplification    : 0.16
% 17.89/9.57  Subsumption          : 2.07
% 17.89/9.57  Abstraction          : 0.24
% 17.89/9.57  MUC search           : 0.00
% 17.89/9.58  Cooper               : 0.00
% 17.89/9.58  Total                : 8.80
% 17.89/9.58  Index Insertion      : 0.00
% 17.89/9.58  Index Deletion       : 0.00
% 17.89/9.58  Index Matching       : 0.00
% 17.89/9.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
