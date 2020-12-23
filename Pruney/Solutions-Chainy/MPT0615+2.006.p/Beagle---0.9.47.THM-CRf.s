%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:49 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   36 (  48 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   60 (  96 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_47,plain,(
    r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_55,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_20])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(A_20,C_21)
      | ~ r1_tarski(B_22,C_21)
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,(
    ! [A_27,B_28,A_29] :
      ( r1_tarski(A_27,B_28)
      | ~ r1_tarski(A_27,k7_relat_1(B_28,A_29))
      | ~ v1_relat_1(B_28) ) ),
    inference(resolution,[status(thm)],[c_12,c_40])).

tff(c_96,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_87])).

tff(c_110,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_96])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_110])).

tff(c_113,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [B_34,A_35] :
      ( k7_relat_1(B_34,A_35) = B_34
      | ~ r1_tarski(k1_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_164,plain,(
    ! [B_34] :
      ( k7_relat_1(B_34,k1_relat_1(B_34)) = B_34
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_6,c_154])).

tff(c_193,plain,(
    ! [B_41,A_42,C_43] :
      ( r1_tarski(k7_relat_1(B_41,A_42),k7_relat_1(C_43,A_42))
      | ~ r1_tarski(B_41,C_43)
      | ~ v1_relat_1(C_43)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_339,plain,(
    ! [B_62,C_63] :
      ( r1_tarski(B_62,k7_relat_1(C_63,k1_relat_1(B_62)))
      | ~ r1_tarski(B_62,C_63)
      | ~ v1_relat_1(C_63)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_193])).

tff(c_114,plain,(
    ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_365,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_339,c_114])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_113,c_365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.35  
% 2.41/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.35  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.41/1.35  
% 2.41/1.35  %Foreground sorts:
% 2.41/1.35  
% 2.41/1.35  
% 2.41/1.35  %Background operators:
% 2.41/1.35  
% 2.41/1.35  
% 2.41/1.35  %Foreground operators:
% 2.41/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.41/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.41/1.35  
% 2.41/1.36  tff(f_66, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t219_relat_1)).
% 2.41/1.36  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.41/1.36  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.41/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.41/1.36  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.41/1.36  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 2.41/1.36  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.36  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.36  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2') | r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.36  tff(c_47, plain, (r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_26])).
% 2.41/1.36  tff(c_20, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1'))) | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.36  tff(c_55, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_20])).
% 2.41/1.36  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.36  tff(c_40, plain, (![A_20, C_21, B_22]: (r1_tarski(A_20, C_21) | ~r1_tarski(B_22, C_21) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.41/1.36  tff(c_87, plain, (![A_27, B_28, A_29]: (r1_tarski(A_27, B_28) | ~r1_tarski(A_27, k7_relat_1(B_28, A_29)) | ~v1_relat_1(B_28))), inference(resolution, [status(thm)], [c_12, c_40])).
% 2.41/1.36  tff(c_96, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_47, c_87])).
% 2.41/1.36  tff(c_110, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_96])).
% 2.41/1.36  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_110])).
% 2.41/1.36  tff(c_113, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 2.41/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.36  tff(c_154, plain, (![B_34, A_35]: (k7_relat_1(B_34, A_35)=B_34 | ~r1_tarski(k1_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.41/1.36  tff(c_164, plain, (![B_34]: (k7_relat_1(B_34, k1_relat_1(B_34))=B_34 | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_6, c_154])).
% 2.41/1.36  tff(c_193, plain, (![B_41, A_42, C_43]: (r1_tarski(k7_relat_1(B_41, A_42), k7_relat_1(C_43, A_42)) | ~r1_tarski(B_41, C_43) | ~v1_relat_1(C_43) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.41/1.36  tff(c_339, plain, (![B_62, C_63]: (r1_tarski(B_62, k7_relat_1(C_63, k1_relat_1(B_62))) | ~r1_tarski(B_62, C_63) | ~v1_relat_1(C_63) | ~v1_relat_1(B_62) | ~v1_relat_1(B_62))), inference(superposition, [status(thm), theory('equality')], [c_164, c_193])).
% 2.41/1.36  tff(c_114, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitRight, [status(thm)], [c_26])).
% 2.41/1.36  tff(c_365, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_339, c_114])).
% 2.41/1.36  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_113, c_365])).
% 2.41/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.36  
% 2.41/1.36  Inference rules
% 2.41/1.36  ----------------------
% 2.41/1.36  #Ref     : 0
% 2.41/1.36  #Sup     : 82
% 2.41/1.36  #Fact    : 0
% 2.41/1.36  #Define  : 0
% 2.41/1.36  #Split   : 2
% 2.41/1.36  #Chain   : 0
% 2.41/1.36  #Close   : 0
% 2.41/1.36  
% 2.41/1.36  Ordering : KBO
% 2.41/1.36  
% 2.41/1.36  Simplification rules
% 2.41/1.36  ----------------------
% 2.41/1.36  #Subsume      : 19
% 2.41/1.36  #Demod        : 20
% 2.41/1.36  #Tautology    : 15
% 2.41/1.36  #SimpNegUnit  : 1
% 2.41/1.36  #BackRed      : 0
% 2.41/1.36  
% 2.41/1.36  #Partial instantiations: 0
% 2.41/1.36  #Strategies tried      : 1
% 2.41/1.36  
% 2.41/1.36  Timing (in seconds)
% 2.41/1.36  ----------------------
% 2.41/1.36  Preprocessing        : 0.29
% 2.41/1.36  Parsing              : 0.16
% 2.41/1.36  CNF conversion       : 0.02
% 2.41/1.36  Main loop            : 0.26
% 2.41/1.36  Inferencing          : 0.10
% 2.41/1.36  Reduction            : 0.07
% 2.41/1.36  Demodulation         : 0.05
% 2.41/1.36  BG Simplification    : 0.01
% 2.41/1.36  Subsumption          : 0.07
% 2.41/1.36  Abstraction          : 0.01
% 2.41/1.36  MUC search           : 0.00
% 2.41/1.36  Cooper               : 0.00
% 2.41/1.36  Total                : 0.58
% 2.41/1.36  Index Insertion      : 0.00
% 2.41/1.36  Index Deletion       : 0.00
% 2.41/1.36  Index Matching       : 0.00
% 2.41/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
