%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:19 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
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
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k8_relat_1(A_8,B_9),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25,plain,(
    ! [A_22,B_23] :
      ( k2_xboole_0(A_22,B_23) = B_23
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(k8_relat_1(A_30,B_31),B_31) = B_31
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_8,c_25])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [A_30,B_31,C_3] :
      ( r1_tarski(k8_relat_1(A_30,B_31),C_3)
      | ~ r1_tarski(B_31,C_3)
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [B_11,A_10,C_12] :
      ( k8_relat_1(B_11,k8_relat_1(A_10,C_12)) = k8_relat_1(A_10,C_12)
      | ~ r1_tarski(A_10,B_11)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_114,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(k8_relat_1(A_38,B_39),k8_relat_1(A_38,C_40))
      | ~ r1_tarski(B_39,C_40)
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1449,plain,(
    ! [A_126,C_127,B_128,C_129] :
      ( r1_tarski(k8_relat_1(A_126,C_127),k8_relat_1(B_128,C_129))
      | ~ r1_tarski(k8_relat_1(A_126,C_127),C_129)
      | ~ v1_relat_1(C_129)
      | ~ v1_relat_1(k8_relat_1(A_126,C_127))
      | ~ r1_tarski(A_126,B_128)
      | ~ v1_relat_1(C_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_114])).

tff(c_14,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1471,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1449,c_14])).

tff(c_1501,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_20,c_1471])).

tff(c_1541,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1501])).

tff(c_1544,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1541])).

tff(c_1548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1544])).

tff(c_1549,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1501])).

tff(c_1620,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1549])).

tff(c_1633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_1620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.05/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.69  
% 4.05/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.69  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.05/1.69  
% 4.05/1.69  %Foreground sorts:
% 4.05/1.69  
% 4.05/1.69  
% 4.05/1.69  %Background operators:
% 4.05/1.69  
% 4.05/1.69  
% 4.05/1.69  %Foreground operators:
% 4.05/1.69  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.05/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.05/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.05/1.69  tff('#skF_2', type, '#skF_2': $i).
% 4.05/1.69  tff('#skF_3', type, '#skF_3': $i).
% 4.05/1.69  tff('#skF_1', type, '#skF_1': $i).
% 4.05/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.05/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.05/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.05/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.05/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.05/1.69  
% 4.05/1.70  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_relat_1)).
% 4.05/1.70  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 4.05/1.70  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.05/1.70  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.05/1.70  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 4.05/1.70  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 4.05/1.70  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_relat_1)).
% 4.05/1.70  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.05/1.70  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.05/1.70  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k8_relat_1(A_8, B_9), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.05/1.70  tff(c_25, plain, (![A_22, B_23]: (k2_xboole_0(A_22, B_23)=B_23 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.05/1.70  tff(c_60, plain, (![A_30, B_31]: (k2_xboole_0(k8_relat_1(A_30, B_31), B_31)=B_31 | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_8, c_25])).
% 4.05/1.70  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.05/1.70  tff(c_66, plain, (![A_30, B_31, C_3]: (r1_tarski(k8_relat_1(A_30, B_31), C_3) | ~r1_tarski(B_31, C_3) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2])).
% 4.05/1.70  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.05/1.70  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.05/1.70  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.05/1.70  tff(c_10, plain, (![B_11, A_10, C_12]: (k8_relat_1(B_11, k8_relat_1(A_10, C_12))=k8_relat_1(A_10, C_12) | ~r1_tarski(A_10, B_11) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.05/1.70  tff(c_114, plain, (![A_38, B_39, C_40]: (r1_tarski(k8_relat_1(A_38, B_39), k8_relat_1(A_38, C_40)) | ~r1_tarski(B_39, C_40) | ~v1_relat_1(C_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.05/1.70  tff(c_1449, plain, (![A_126, C_127, B_128, C_129]: (r1_tarski(k8_relat_1(A_126, C_127), k8_relat_1(B_128, C_129)) | ~r1_tarski(k8_relat_1(A_126, C_127), C_129) | ~v1_relat_1(C_129) | ~v1_relat_1(k8_relat_1(A_126, C_127)) | ~r1_tarski(A_126, B_128) | ~v1_relat_1(C_127))), inference(superposition, [status(thm), theory('equality')], [c_10, c_114])).
% 4.05/1.70  tff(c_14, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.05/1.70  tff(c_1471, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1449, c_14])).
% 4.05/1.70  tff(c_1501, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_4') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_20, c_1471])).
% 4.05/1.70  tff(c_1541, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1501])).
% 4.05/1.70  tff(c_1544, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1541])).
% 4.05/1.70  tff(c_1548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1544])).
% 4.05/1.70  tff(c_1549, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_1501])).
% 4.05/1.70  tff(c_1620, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1549])).
% 4.05/1.70  tff(c_1633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_1620])).
% 4.05/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.70  
% 4.05/1.70  Inference rules
% 4.05/1.70  ----------------------
% 4.05/1.70  #Ref     : 0
% 4.05/1.70  #Sup     : 430
% 4.05/1.70  #Fact    : 0
% 4.05/1.71  #Define  : 0
% 4.05/1.71  #Split   : 5
% 4.05/1.71  #Chain   : 0
% 4.05/1.71  #Close   : 0
% 4.05/1.71  
% 4.05/1.71  Ordering : KBO
% 4.05/1.71  
% 4.05/1.71  Simplification rules
% 4.05/1.71  ----------------------
% 4.05/1.71  #Subsume      : 106
% 4.05/1.71  #Demod        : 30
% 4.05/1.71  #Tautology    : 114
% 4.05/1.71  #SimpNegUnit  : 0
% 4.05/1.71  #BackRed      : 0
% 4.05/1.71  
% 4.05/1.71  #Partial instantiations: 0
% 4.05/1.71  #Strategies tried      : 1
% 4.05/1.71  
% 4.05/1.71  Timing (in seconds)
% 4.05/1.71  ----------------------
% 4.05/1.71  Preprocessing        : 0.28
% 4.05/1.71  Parsing              : 0.15
% 4.05/1.71  CNF conversion       : 0.02
% 4.05/1.71  Main loop            : 0.66
% 4.05/1.71  Inferencing          : 0.23
% 4.05/1.71  Reduction            : 0.15
% 4.05/1.71  Demodulation         : 0.10
% 4.05/1.71  BG Simplification    : 0.03
% 4.05/1.71  Subsumption          : 0.19
% 4.05/1.71  Abstraction          : 0.03
% 4.05/1.71  MUC search           : 0.00
% 4.05/1.71  Cooper               : 0.00
% 4.05/1.71  Total                : 0.96
% 4.05/1.71  Index Insertion      : 0.00
% 4.05/1.71  Index Deletion       : 0.00
% 4.05/1.71  Index Matching       : 0.00
% 4.05/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
