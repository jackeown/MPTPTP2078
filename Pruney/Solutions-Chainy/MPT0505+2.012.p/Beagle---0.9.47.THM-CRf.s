%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:52 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  53 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski('#skF_1'(A_5,B_6,C_7),B_6)
      | k3_xboole_0(B_6,C_7) = A_5
      | ~ r1_tarski(A_5,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_126,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_tarski('#skF_1'(A_37,B_38,C_39),A_37)
      | k3_xboole_0(B_38,C_39) = A_37
      | ~ r1_tarski(A_37,C_39)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_130,plain,(
    ! [B_6,C_7] :
      ( k3_xboole_0(B_6,C_7) = B_6
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(B_6,B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_126])).

tff(c_145,plain,(
    ! [B_43,C_44] :
      ( k3_xboole_0(B_43,C_44) = B_43
      | ~ r1_tarski(B_43,C_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_130])).

tff(c_163,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_145])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_176,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_102,plain,(
    ! [C_31,A_32,B_33] :
      ( k7_relat_1(k7_relat_1(C_31,A_32),B_33) = k7_relat_1(C_31,k3_xboole_0(A_32,B_33))
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') != k7_relat_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_111,plain,
    ( k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')) != k7_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_24])).

tff(c_120,plain,(
    k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')) != k7_relat_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_111])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.93/1.19  
% 1.93/1.19  %Foreground sorts:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Background operators:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Foreground operators:
% 1.93/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.93/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.93/1.19  
% 1.93/1.20  tff(f_63, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 1.93/1.20  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.93/1.20  tff(f_46, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 1.93/1.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.93/1.20  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.93/1.20  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.20  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.20  tff(c_14, plain, (![A_5, B_6, C_7]: (r1_tarski('#skF_1'(A_5, B_6, C_7), B_6) | k3_xboole_0(B_6, C_7)=A_5 | ~r1_tarski(A_5, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.20  tff(c_126, plain, (![A_37, B_38, C_39]: (~r1_tarski('#skF_1'(A_37, B_38, C_39), A_37) | k3_xboole_0(B_38, C_39)=A_37 | ~r1_tarski(A_37, C_39) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.20  tff(c_130, plain, (![B_6, C_7]: (k3_xboole_0(B_6, C_7)=B_6 | ~r1_tarski(B_6, C_7) | ~r1_tarski(B_6, B_6))), inference(resolution, [status(thm)], [c_14, c_126])).
% 1.93/1.20  tff(c_145, plain, (![B_43, C_44]: (k3_xboole_0(B_43, C_44)=B_43 | ~r1_tarski(B_43, C_44))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_130])).
% 1.93/1.20  tff(c_163, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_145])).
% 1.93/1.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.20  tff(c_176, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_163, c_2])).
% 1.93/1.20  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.20  tff(c_102, plain, (![C_31, A_32, B_33]: (k7_relat_1(k7_relat_1(C_31, A_32), B_33)=k7_relat_1(C_31, k3_xboole_0(A_32, B_33)) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.20  tff(c_24, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')!=k7_relat_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.20  tff(c_111, plain, (k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))!=k7_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_102, c_24])).
% 1.93/1.20  tff(c_120, plain, (k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))!=k7_relat_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_111])).
% 1.93/1.20  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_120])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 37
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 1
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 0
% 1.93/1.20  #Demod        : 8
% 1.93/1.20  #Tautology    : 22
% 1.93/1.20  #SimpNegUnit  : 0
% 1.93/1.20  #BackRed      : 1
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.20  Preprocessing        : 0.29
% 1.93/1.20  Parsing              : 0.15
% 1.93/1.20  CNF conversion       : 0.02
% 1.93/1.20  Main loop            : 0.16
% 1.93/1.20  Inferencing          : 0.06
% 1.93/1.20  Reduction            : 0.05
% 1.93/1.20  Demodulation         : 0.04
% 1.93/1.20  BG Simplification    : 0.01
% 1.93/1.20  Subsumption          : 0.03
% 1.93/1.20  Abstraction          : 0.01
% 1.93/1.20  MUC search           : 0.00
% 1.93/1.20  Cooper               : 0.00
% 1.93/1.20  Total                : 0.47
% 1.93/1.20  Index Insertion      : 0.00
% 1.93/1.20  Index Deletion       : 0.00
% 1.93/1.20  Index Matching       : 0.00
% 1.93/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
