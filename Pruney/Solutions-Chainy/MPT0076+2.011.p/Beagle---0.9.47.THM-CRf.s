%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:33 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   35 (  41 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_45,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_45])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_14])).

tff(c_61,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_76,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_61])).

tff(c_85,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_76])).

tff(c_116,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_122,plain,(
    ! [C_30] :
      ( ~ r1_xboole_0('#skF_4','#skF_3')
      | ~ r2_hidden(C_30,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_116])).

tff(c_130,plain,(
    ! [C_31] : ~ r2_hidden(C_31,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_122])).

tff(c_134,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.25  
% 1.85/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.85/1.25  
% 1.85/1.25  %Foreground sorts:
% 1.85/1.25  
% 1.85/1.25  
% 1.85/1.25  %Background operators:
% 1.85/1.25  
% 1.85/1.25  
% 1.85/1.25  %Foreground operators:
% 1.85/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.85/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.85/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.85/1.25  
% 1.85/1.26  tff(f_64, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.85/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.85/1.26  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.85/1.26  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.85/1.26  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.85/1.26  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.85/1.26  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.85/1.26  tff(c_22, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.85/1.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.26  tff(c_18, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.85/1.26  tff(c_12, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.85/1.26  tff(c_20, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.85/1.26  tff(c_45, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.85/1.26  tff(c_49, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_20, c_45])).
% 1.85/1.26  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.85/1.26  tff(c_53, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_49, c_14])).
% 1.85/1.26  tff(c_61, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.85/1.26  tff(c_76, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_53, c_61])).
% 1.85/1.26  tff(c_85, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_76])).
% 1.85/1.26  tff(c_116, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.85/1.26  tff(c_122, plain, (![C_30]: (~r1_xboole_0('#skF_4', '#skF_3') | ~r2_hidden(C_30, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_116])).
% 1.85/1.26  tff(c_130, plain, (![C_31]: (~r2_hidden(C_31, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_122])).
% 1.85/1.26  tff(c_134, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_130])).
% 1.85/1.26  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_134])).
% 1.85/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.26  
% 1.85/1.26  Inference rules
% 1.85/1.26  ----------------------
% 1.85/1.26  #Ref     : 0
% 1.85/1.26  #Sup     : 31
% 1.85/1.26  #Fact    : 0
% 1.85/1.26  #Define  : 0
% 1.85/1.26  #Split   : 0
% 1.85/1.26  #Chain   : 0
% 1.85/1.26  #Close   : 0
% 1.85/1.26  
% 1.85/1.26  Ordering : KBO
% 1.85/1.26  
% 1.85/1.26  Simplification rules
% 1.85/1.26  ----------------------
% 1.85/1.26  #Subsume      : 0
% 1.85/1.26  #Demod        : 4
% 1.85/1.26  #Tautology    : 18
% 1.85/1.26  #SimpNegUnit  : 1
% 1.85/1.26  #BackRed      : 0
% 1.85/1.26  
% 1.85/1.26  #Partial instantiations: 0
% 1.85/1.26  #Strategies tried      : 1
% 1.85/1.26  
% 1.85/1.26  Timing (in seconds)
% 1.85/1.26  ----------------------
% 1.85/1.26  Preprocessing        : 0.31
% 1.85/1.26  Parsing              : 0.17
% 1.85/1.26  CNF conversion       : 0.02
% 1.85/1.26  Main loop            : 0.12
% 1.85/1.26  Inferencing          : 0.06
% 1.85/1.26  Reduction            : 0.04
% 1.85/1.26  Demodulation         : 0.03
% 1.85/1.26  BG Simplification    : 0.01
% 1.85/1.26  Subsumption          : 0.02
% 1.85/1.26  Abstraction          : 0.01
% 1.85/1.26  MUC search           : 0.00
% 1.85/1.26  Cooper               : 0.00
% 1.85/1.26  Total                : 0.46
% 1.85/1.26  Index Insertion      : 0.00
% 1.85/1.26  Index Deletion       : 0.00
% 1.85/1.26  Index Matching       : 0.00
% 1.85/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
