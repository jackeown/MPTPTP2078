%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:17 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  86 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r1_tarski(A,B)
         => ( k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A)
            & k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_459,plain,(
    ! [C_74,B_75,A_76] :
      ( k7_relat_1(k7_relat_1(C_74,B_75),A_76) = k7_relat_1(C_74,A_76)
      | ~ r1_tarski(A_76,B_75)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_27,plain,(
    ! [B_19,A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_19,A_20)),A_20)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [B_25,A_26] :
      ( k2_xboole_0(k1_relat_1(k7_relat_1(B_25,A_26)),A_26) = A_26
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_27,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [B_29,A_30,C_31] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_29,A_30)),C_31)
      | ~ r1_tarski(A_30,C_31)
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_329,plain,(
    ! [B_64,A_65,C_66] :
      ( k7_relat_1(k7_relat_1(B_64,A_65),C_66) = k7_relat_1(B_64,A_65)
      | ~ v1_relat_1(k7_relat_1(B_64,A_65))
      | ~ r1_tarski(A_65,C_66)
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_59,c_12])).

tff(c_337,plain,(
    ! [A_67,B_68,C_69] :
      ( k7_relat_1(k7_relat_1(A_67,B_68),C_69) = k7_relat_1(A_67,B_68)
      | ~ r1_tarski(B_68,C_69)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_6,c_329])).

tff(c_14,plain,
    ( k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1')
    | k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_41,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_384,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_41])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_384])).

tff(c_417,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_474,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_417])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.22/1.31  
% 2.22/1.31  %Foreground sorts:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Background operators:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Foreground operators:
% 2.22/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.22/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.31  
% 2.22/1.32  tff(f_64, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A)) & (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_funct_1)).
% 2.22/1.32  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 2.22/1.32  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.22/1.32  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.22/1.32  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.22/1.32  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.22/1.32  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.22/1.32  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.22/1.32  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.22/1.32  tff(c_459, plain, (![C_74, B_75, A_76]: (k7_relat_1(k7_relat_1(C_74, B_75), A_76)=k7_relat_1(C_74, A_76) | ~r1_tarski(A_76, B_75) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.32  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.32  tff(c_27, plain, (![B_19, A_20]: (r1_tarski(k1_relat_1(k7_relat_1(B_19, A_20)), A_20) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.32  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.32  tff(c_42, plain, (![B_25, A_26]: (k2_xboole_0(k1_relat_1(k7_relat_1(B_25, A_26)), A_26)=A_26 | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_27, c_4])).
% 2.22/1.32  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.32  tff(c_59, plain, (![B_29, A_30, C_31]: (r1_tarski(k1_relat_1(k7_relat_1(B_29, A_30)), C_31) | ~r1_tarski(A_30, C_31) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2])).
% 2.22/1.32  tff(c_12, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~r1_tarski(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.32  tff(c_329, plain, (![B_64, A_65, C_66]: (k7_relat_1(k7_relat_1(B_64, A_65), C_66)=k7_relat_1(B_64, A_65) | ~v1_relat_1(k7_relat_1(B_64, A_65)) | ~r1_tarski(A_65, C_66) | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_59, c_12])).
% 2.22/1.32  tff(c_337, plain, (![A_67, B_68, C_69]: (k7_relat_1(k7_relat_1(A_67, B_68), C_69)=k7_relat_1(A_67, B_68) | ~r1_tarski(B_68, C_69) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_6, c_329])).
% 2.22/1.32  tff(c_14, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1') | k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.22/1.32  tff(c_41, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_14])).
% 2.22/1.32  tff(c_384, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_337, c_41])).
% 2.22/1.32  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_384])).
% 2.22/1.32  tff(c_417, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_14])).
% 2.22/1.32  tff(c_474, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_459, c_417])).
% 2.22/1.32  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_474])).
% 2.22/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.32  
% 2.22/1.32  Inference rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Ref     : 0
% 2.22/1.32  #Sup     : 130
% 2.22/1.32  #Fact    : 0
% 2.22/1.32  #Define  : 0
% 2.22/1.32  #Split   : 3
% 2.22/1.32  #Chain   : 0
% 2.22/1.32  #Close   : 0
% 2.22/1.32  
% 2.22/1.32  Ordering : KBO
% 2.22/1.32  
% 2.22/1.32  Simplification rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Subsume      : 27
% 2.22/1.32  #Demod        : 7
% 2.22/1.32  #Tautology    : 39
% 2.22/1.32  #SimpNegUnit  : 0
% 2.22/1.33  #BackRed      : 0
% 2.22/1.33  
% 2.22/1.33  #Partial instantiations: 0
% 2.22/1.33  #Strategies tried      : 1
% 2.22/1.33  
% 2.22/1.33  Timing (in seconds)
% 2.22/1.33  ----------------------
% 2.22/1.33  Preprocessing        : 0.27
% 2.22/1.33  Parsing              : 0.15
% 2.22/1.33  CNF conversion       : 0.02
% 2.22/1.33  Main loop            : 0.29
% 2.22/1.33  Inferencing          : 0.12
% 2.22/1.33  Reduction            : 0.06
% 2.22/1.33  Demodulation         : 0.04
% 2.22/1.33  BG Simplification    : 0.02
% 2.22/1.33  Subsumption          : 0.06
% 2.22/1.33  Abstraction          : 0.02
% 2.22/1.33  MUC search           : 0.00
% 2.22/1.33  Cooper               : 0.00
% 2.22/1.33  Total                : 0.58
% 2.22/1.33  Index Insertion      : 0.00
% 2.22/1.33  Index Deletion       : 0.00
% 2.22/1.33  Index Matching       : 0.00
% 2.22/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
