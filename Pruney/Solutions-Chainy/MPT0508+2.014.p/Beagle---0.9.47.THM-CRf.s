%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:56 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :   40 (  63 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 148 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

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

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_41,plain,(
    ! [B_22,A_23] :
      ( r1_tarski(k7_relat_1(B_22,A_23),B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [B_30,A_31] :
      ( k2_xboole_0(k7_relat_1(B_30,A_31),B_30) = B_30
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_41,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [B_30,A_31,C_3] :
      ( r1_tarski(k7_relat_1(B_30,A_31),C_3)
      | ~ r1_tarski(B_30,C_3)
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [C_10,A_8,B_9] :
      ( k7_relat_1(k7_relat_1(C_10,A_8),B_9) = k7_relat_1(C_10,A_8)
      | ~ r1_tarski(A_8,B_9)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_114,plain,(
    ! [B_38,A_39,C_40] :
      ( r1_tarski(k7_relat_1(B_38,A_39),k7_relat_1(C_40,A_39))
      | ~ r1_tarski(B_38,C_40)
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1449,plain,(
    ! [C_126,A_127,C_128,B_129] :
      ( r1_tarski(k7_relat_1(C_126,A_127),k7_relat_1(C_128,B_129))
      | ~ r1_tarski(k7_relat_1(C_126,A_127),C_128)
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(k7_relat_1(C_126,A_127))
      | ~ r1_tarski(A_127,B_129)
      | ~ v1_relat_1(C_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_114])).

tff(c_14,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1468,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1449,c_14])).

tff(c_1500,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_20,c_1468])).

tff(c_1541,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1500])).

tff(c_1544,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1541])).

tff(c_1548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1544])).

tff(c_1549,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1500])).

tff(c_1620,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1549])).

tff(c_1633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_1620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.74  
% 4.26/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.74  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.26/1.74  
% 4.26/1.74  %Foreground sorts:
% 4.26/1.74  
% 4.26/1.74  
% 4.26/1.74  %Background operators:
% 4.26/1.74  
% 4.26/1.74  
% 4.26/1.74  %Foreground operators:
% 4.26/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.26/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.26/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.26/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.26/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.26/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.26/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.26/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.26/1.74  
% 4.26/1.75  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 4.26/1.75  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 4.26/1.75  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.26/1.75  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.26/1.75  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.26/1.75  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 4.26/1.75  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 4.26/1.75  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.26/1.75  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.26/1.75  tff(c_41, plain, (![B_22, A_23]: (r1_tarski(k7_relat_1(B_22, A_23), B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.26/1.75  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.26/1.75  tff(c_60, plain, (![B_30, A_31]: (k2_xboole_0(k7_relat_1(B_30, A_31), B_30)=B_30 | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_41, c_4])).
% 4.26/1.75  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.26/1.75  tff(c_66, plain, (![B_30, A_31, C_3]: (r1_tarski(k7_relat_1(B_30, A_31), C_3) | ~r1_tarski(B_30, C_3) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2])).
% 4.26/1.75  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.26/1.75  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.26/1.75  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.26/1.75  tff(c_8, plain, (![C_10, A_8, B_9]: (k7_relat_1(k7_relat_1(C_10, A_8), B_9)=k7_relat_1(C_10, A_8) | ~r1_tarski(A_8, B_9) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.26/1.75  tff(c_114, plain, (![B_38, A_39, C_40]: (r1_tarski(k7_relat_1(B_38, A_39), k7_relat_1(C_40, A_39)) | ~r1_tarski(B_38, C_40) | ~v1_relat_1(C_40) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.26/1.75  tff(c_1449, plain, (![C_126, A_127, C_128, B_129]: (r1_tarski(k7_relat_1(C_126, A_127), k7_relat_1(C_128, B_129)) | ~r1_tarski(k7_relat_1(C_126, A_127), C_128) | ~v1_relat_1(C_128) | ~v1_relat_1(k7_relat_1(C_126, A_127)) | ~r1_tarski(A_127, B_129) | ~v1_relat_1(C_126))), inference(superposition, [status(thm), theory('equality')], [c_8, c_114])).
% 4.26/1.75  tff(c_14, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.26/1.75  tff(c_1468, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1449, c_14])).
% 4.26/1.75  tff(c_1500, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_20, c_1468])).
% 4.26/1.75  tff(c_1541, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1500])).
% 4.26/1.75  tff(c_1544, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1541])).
% 4.26/1.75  tff(c_1548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1544])).
% 4.26/1.75  tff(c_1549, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_4')), inference(splitRight, [status(thm)], [c_1500])).
% 4.26/1.75  tff(c_1620, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1549])).
% 4.26/1.75  tff(c_1633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_1620])).
% 4.26/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.75  
% 4.26/1.75  Inference rules
% 4.26/1.75  ----------------------
% 4.26/1.75  #Ref     : 0
% 4.26/1.75  #Sup     : 430
% 4.26/1.75  #Fact    : 0
% 4.26/1.75  #Define  : 0
% 4.26/1.75  #Split   : 5
% 4.26/1.75  #Chain   : 0
% 4.26/1.75  #Close   : 0
% 4.26/1.75  
% 4.26/1.75  Ordering : KBO
% 4.26/1.75  
% 4.26/1.75  Simplification rules
% 4.26/1.75  ----------------------
% 4.26/1.75  #Subsume      : 106
% 4.26/1.75  #Demod        : 30
% 4.26/1.75  #Tautology    : 114
% 4.26/1.75  #SimpNegUnit  : 0
% 4.26/1.75  #BackRed      : 0
% 4.26/1.75  
% 4.26/1.75  #Partial instantiations: 0
% 4.26/1.75  #Strategies tried      : 1
% 4.26/1.75  
% 4.26/1.75  Timing (in seconds)
% 4.26/1.75  ----------------------
% 4.26/1.76  Preprocessing        : 0.30
% 4.26/1.76  Parsing              : 0.17
% 4.26/1.76  CNF conversion       : 0.02
% 4.26/1.76  Main loop            : 0.67
% 4.26/1.76  Inferencing          : 0.24
% 4.26/1.76  Reduction            : 0.15
% 4.26/1.76  Demodulation         : 0.10
% 4.26/1.76  BG Simplification    : 0.03
% 4.26/1.76  Subsumption          : 0.20
% 4.26/1.76  Abstraction          : 0.03
% 4.26/1.76  MUC search           : 0.00
% 4.26/1.76  Cooper               : 0.00
% 4.26/1.76  Total                : 1.00
% 4.26/1.76  Index Insertion      : 0.00
% 4.26/1.76  Index Deletion       : 0.00
% 4.26/1.76  Index Matching       : 0.00
% 4.26/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
