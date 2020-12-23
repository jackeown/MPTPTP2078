%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:50 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  53 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_tarski(A_29,k3_xboole_0(B_30,C_31))
      | ~ r1_tarski(A_29,C_31)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_21,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(A_13,B_14)
      | ~ r1_tarski(A_13,k3_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [B_14,C_15] : r1_tarski(k3_xboole_0(B_14,C_15),B_14) ),
    inference(resolution,[status(thm)],[c_6,c_21])).

tff(c_33,plain,(
    ! [B_18,A_19] :
      ( B_18 = A_19
      | ~ r1_tarski(B_18,A_19)
      | ~ r1_tarski(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [B_14,C_15] :
      ( k3_xboole_0(B_14,C_15) = B_14
      | ~ r1_tarski(B_14,k3_xboole_0(B_14,C_15)) ) ),
    inference(resolution,[status(thm)],[c_26,c_33])).

tff(c_70,plain,(
    ! [B_30,C_31] :
      ( k3_xboole_0(B_30,C_31) = B_30
      | ~ r1_tarski(B_30,C_31)
      | ~ r1_tarski(B_30,B_30) ) ),
    inference(resolution,[status(thm)],[c_66,c_40])).

tff(c_81,plain,(
    ! [B_32,C_33] :
      ( k3_xboole_0(B_32,C_33) = B_32
      | ~ r1_tarski(B_32,C_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_105,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_81])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_153,plain,(
    ! [C_35,A_36,B_37] :
      ( k7_relat_1(k7_relat_1(C_35,A_36),B_37) = k7_relat_1(C_35,k3_xboole_0(A_36,B_37))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_162,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_14])).

tff(c_171,plain,(
    k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_162])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:09:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.26  
% 1.86/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.26  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.86/1.26  
% 1.86/1.26  %Foreground sorts:
% 1.86/1.26  
% 1.86/1.26  
% 1.86/1.26  %Background operators:
% 1.86/1.26  
% 1.86/1.26  
% 1.86/1.26  %Foreground operators:
% 1.86/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.86/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.26  
% 1.96/1.27  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.96/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.96/1.27  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.96/1.27  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.96/1.27  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.96/1.27  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.27  tff(c_66, plain, (![A_29, B_30, C_31]: (r1_tarski(A_29, k3_xboole_0(B_30, C_31)) | ~r1_tarski(A_29, C_31) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.27  tff(c_21, plain, (![A_13, B_14, C_15]: (r1_tarski(A_13, B_14) | ~r1_tarski(A_13, k3_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.27  tff(c_26, plain, (![B_14, C_15]: (r1_tarski(k3_xboole_0(B_14, C_15), B_14))), inference(resolution, [status(thm)], [c_6, c_21])).
% 1.96/1.27  tff(c_33, plain, (![B_18, A_19]: (B_18=A_19 | ~r1_tarski(B_18, A_19) | ~r1_tarski(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.27  tff(c_40, plain, (![B_14, C_15]: (k3_xboole_0(B_14, C_15)=B_14 | ~r1_tarski(B_14, k3_xboole_0(B_14, C_15)))), inference(resolution, [status(thm)], [c_26, c_33])).
% 1.96/1.27  tff(c_70, plain, (![B_30, C_31]: (k3_xboole_0(B_30, C_31)=B_30 | ~r1_tarski(B_30, C_31) | ~r1_tarski(B_30, B_30))), inference(resolution, [status(thm)], [c_66, c_40])).
% 1.96/1.27  tff(c_81, plain, (![B_32, C_33]: (k3_xboole_0(B_32, C_33)=B_32 | ~r1_tarski(B_32, C_33))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_70])).
% 1.96/1.27  tff(c_105, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_16, c_81])).
% 1.96/1.27  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.27  tff(c_153, plain, (![C_35, A_36, B_37]: (k7_relat_1(k7_relat_1(C_35, A_36), B_37)=k7_relat_1(C_35, k3_xboole_0(A_36, B_37)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.27  tff(c_14, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.27  tff(c_162, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_153, c_14])).
% 1.96/1.27  tff(c_171, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_162])).
% 1.96/1.27  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_171])).
% 1.96/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.27  
% 1.96/1.27  Inference rules
% 1.96/1.27  ----------------------
% 1.96/1.27  #Ref     : 0
% 1.96/1.27  #Sup     : 42
% 1.96/1.27  #Fact    : 0
% 1.96/1.27  #Define  : 0
% 1.96/1.27  #Split   : 1
% 1.96/1.27  #Chain   : 0
% 1.96/1.27  #Close   : 0
% 1.96/1.27  
% 1.96/1.27  Ordering : KBO
% 1.96/1.27  
% 1.96/1.27  Simplification rules
% 1.96/1.27  ----------------------
% 1.96/1.27  #Subsume      : 0
% 1.96/1.27  #Demod        : 18
% 1.96/1.27  #Tautology    : 24
% 1.96/1.27  #SimpNegUnit  : 0
% 1.96/1.27  #BackRed      : 0
% 1.96/1.27  
% 1.96/1.27  #Partial instantiations: 0
% 1.96/1.27  #Strategies tried      : 1
% 1.96/1.27  
% 1.96/1.27  Timing (in seconds)
% 1.96/1.27  ----------------------
% 1.96/1.28  Preprocessing        : 0.28
% 1.96/1.28  Parsing              : 0.15
% 1.96/1.28  CNF conversion       : 0.02
% 1.96/1.28  Main loop            : 0.17
% 1.96/1.28  Inferencing          : 0.07
% 1.96/1.28  Reduction            : 0.05
% 1.96/1.28  Demodulation         : 0.04
% 1.96/1.28  BG Simplification    : 0.01
% 1.96/1.28  Subsumption          : 0.04
% 1.96/1.28  Abstraction          : 0.01
% 1.96/1.28  MUC search           : 0.00
% 1.96/1.28  Cooper               : 0.00
% 1.96/1.28  Total                : 0.47
% 1.96/1.28  Index Insertion      : 0.00
% 1.96/1.28  Index Deletion       : 0.00
% 1.96/1.28  Index Matching       : 0.00
% 1.96/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
