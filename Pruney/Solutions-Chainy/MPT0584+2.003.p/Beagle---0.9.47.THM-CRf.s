%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:00 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  55 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_44,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C,D] :
                ( ( r1_tarski(C,D)
                  & k7_relat_1(A,D) = k7_relat_1(B,D) )
               => k7_relat_1(A,C) = k7_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t188_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(c_4,plain,(
    k7_relat_1('#skF_2','#skF_3') != k7_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17,plain,(
    ! [C_11,B_12,A_13] :
      ( k7_relat_1(k7_relat_1(C_11,B_12),A_13) = k7_relat_1(C_11,A_13)
      | ~ r1_tarski(A_13,B_12)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_13] :
      ( k7_relat_1(k7_relat_1('#skF_1','#skF_4'),A_13) = k7_relat_1('#skF_2',A_13)
      | ~ r1_tarski(A_13,'#skF_4')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_17])).

tff(c_37,plain,(
    ! [A_14] :
      ( k7_relat_1(k7_relat_1('#skF_1','#skF_4'),A_14) = k7_relat_1('#skF_2',A_14)
      | ~ r1_tarski(A_14,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( k7_relat_1(k7_relat_1(C_3,B_2),A_1) = k7_relat_1(C_3,A_1)
      | ~ r1_tarski(A_1,B_2)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_2',A_14) = k7_relat_1('#skF_1',A_14)
      | ~ r1_tarski(A_14,'#skF_4')
      | ~ v1_relat_1('#skF_1')
      | ~ r1_tarski(A_14,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_2])).

tff(c_60,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_2',A_15) = k7_relat_1('#skF_1',A_15)
      | ~ r1_tarski(A_15,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_63,plain,(
    k7_relat_1('#skF_2','#skF_3') = k7_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_60])).

tff(c_67,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:48:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.44  
% 1.92/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.45  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.92/1.45  
% 1.92/1.45  %Foreground sorts:
% 1.92/1.45  
% 1.92/1.45  
% 1.92/1.45  %Background operators:
% 1.92/1.45  
% 1.92/1.45  
% 1.92/1.45  %Foreground operators:
% 1.92/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.92/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.45  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.45  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.45  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.45  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.45  
% 2.08/1.46  tff(f_44, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C, D]: ((r1_tarski(C, D) & (k7_relat_1(A, D) = k7_relat_1(B, D))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t188_relat_1)).
% 2.08/1.46  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.08/1.46  tff(c_4, plain, (k7_relat_1('#skF_2', '#skF_3')!=k7_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.46  tff(c_8, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.46  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.46  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.46  tff(c_6, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.46  tff(c_17, plain, (![C_11, B_12, A_13]: (k7_relat_1(k7_relat_1(C_11, B_12), A_13)=k7_relat_1(C_11, A_13) | ~r1_tarski(A_13, B_12) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.46  tff(c_32, plain, (![A_13]: (k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), A_13)=k7_relat_1('#skF_2', A_13) | ~r1_tarski(A_13, '#skF_4') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_17])).
% 2.08/1.46  tff(c_37, plain, (![A_14]: (k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), A_14)=k7_relat_1('#skF_2', A_14) | ~r1_tarski(A_14, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 2.08/1.46  tff(c_2, plain, (![C_3, B_2, A_1]: (k7_relat_1(k7_relat_1(C_3, B_2), A_1)=k7_relat_1(C_3, A_1) | ~r1_tarski(A_1, B_2) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.46  tff(c_46, plain, (![A_14]: (k7_relat_1('#skF_2', A_14)=k7_relat_1('#skF_1', A_14) | ~r1_tarski(A_14, '#skF_4') | ~v1_relat_1('#skF_1') | ~r1_tarski(A_14, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_2])).
% 2.08/1.46  tff(c_60, plain, (![A_15]: (k7_relat_1('#skF_2', A_15)=k7_relat_1('#skF_1', A_15) | ~r1_tarski(A_15, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 2.08/1.46  tff(c_63, plain, (k7_relat_1('#skF_2', '#skF_3')=k7_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_60])).
% 2.08/1.46  tff(c_67, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_63])).
% 2.08/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.46  
% 2.08/1.46  Inference rules
% 2.08/1.46  ----------------------
% 2.08/1.46  #Ref     : 0
% 2.08/1.46  #Sup     : 13
% 2.08/1.46  #Fact    : 0
% 2.08/1.46  #Define  : 0
% 2.08/1.46  #Split   : 0
% 2.08/1.46  #Chain   : 0
% 2.08/1.46  #Close   : 0
% 2.08/1.46  
% 2.08/1.46  Ordering : KBO
% 2.08/1.46  
% 2.08/1.46  Simplification rules
% 2.08/1.46  ----------------------
% 2.08/1.46  #Subsume      : 0
% 2.08/1.46  #Demod        : 3
% 2.08/1.46  #Tautology    : 6
% 2.08/1.46  #SimpNegUnit  : 1
% 2.08/1.46  #BackRed      : 0
% 2.08/1.46  
% 2.08/1.46  #Partial instantiations: 0
% 2.08/1.46  #Strategies tried      : 1
% 2.08/1.46  
% 2.08/1.46  Timing (in seconds)
% 2.08/1.46  ----------------------
% 2.08/1.47  Preprocessing        : 0.43
% 2.08/1.47  Parsing              : 0.22
% 2.08/1.47  CNF conversion       : 0.03
% 2.08/1.47  Main loop            : 0.16
% 2.08/1.47  Inferencing          : 0.07
% 2.08/1.47  Reduction            : 0.04
% 2.08/1.47  Demodulation         : 0.03
% 2.08/1.47  BG Simplification    : 0.01
% 2.08/1.47  Subsumption          : 0.02
% 2.08/1.47  Abstraction          : 0.01
% 2.08/1.47  MUC search           : 0.00
% 2.08/1.47  Cooper               : 0.00
% 2.08/1.47  Total                : 0.62
% 2.08/1.47  Index Insertion      : 0.00
% 2.08/1.47  Index Deletion       : 0.00
% 2.08/1.47  Index Matching       : 0.00
% 2.08/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
