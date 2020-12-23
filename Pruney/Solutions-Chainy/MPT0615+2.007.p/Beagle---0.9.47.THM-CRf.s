%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:49 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   42 (  58 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 106 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( ( r1_tarski(k1_relat_1(C),A)
              & r1_tarski(C,B) )
           => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_90,plain,(
    r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_174,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_20])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k7_relat_1(B_13,A_12),B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    ! [B_13,A_12] :
      ( k2_xboole_0(k7_relat_1(B_13,A_12),B_13) = B_13
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_14,c_30])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_94,plain,(
    k2_xboole_0('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) = k7_relat_1('#skF_2',k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_90,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(A_20,C_21)
      | ~ r1_tarski(k2_xboole_0(A_20,B_22),C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_3,B_4,B_25] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_25)) ),
    inference(resolution,[status(thm)],[c_57,c_8])).

tff(c_296,plain,(
    ! [B_47] : r1_tarski('#skF_1',k2_xboole_0(k7_relat_1('#skF_2',k1_relat_1('#skF_1')),B_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_68])).

tff(c_309,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_296])).

tff(c_318,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_309])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_318])).

tff(c_321,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_550,plain,(
    ! [C_61,B_62,A_63] :
      ( r1_tarski(C_61,k7_relat_1(B_62,A_63))
      | ~ r1_tarski(C_61,B_62)
      | ~ r1_tarski(k1_relat_1(C_61),A_63)
      | ~ v1_relat_1(C_61)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_917,plain,(
    ! [C_94,B_95] :
      ( r1_tarski(C_94,k7_relat_1(B_95,k1_relat_1(C_94)))
      | ~ r1_tarski(C_94,B_95)
      | ~ v1_relat_1(C_94)
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_6,c_550])).

tff(c_322,plain,(
    ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_941,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_917,c_322])).

tff(c_964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_321,c_941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:30:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.45  
% 2.49/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.45  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.49/1.45  
% 2.49/1.45  %Foreground sorts:
% 2.49/1.45  
% 2.49/1.45  
% 2.49/1.45  %Background operators:
% 2.49/1.45  
% 2.49/1.45  
% 2.49/1.45  %Foreground operators:
% 2.49/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.49/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.45  
% 2.81/1.46  tff(f_64, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t219_relat_1)).
% 2.81/1.46  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.81/1.46  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.81/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.46  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.81/1.46  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(C, B)) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_relat_1)).
% 2.81/1.46  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.46  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.46  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2') | r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.46  tff(c_90, plain, (r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_26])).
% 2.81/1.46  tff(c_20, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1'))) | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.46  tff(c_174, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_20])).
% 2.81/1.46  tff(c_14, plain, (![B_13, A_12]: (r1_tarski(k7_relat_1(B_13, A_12), B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.46  tff(c_30, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.46  tff(c_37, plain, (![B_13, A_12]: (k2_xboole_0(k7_relat_1(B_13, A_12), B_13)=B_13 | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_14, c_30])).
% 2.81/1.46  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.46  tff(c_94, plain, (k2_xboole_0('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))=k7_relat_1('#skF_2', k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_10])).
% 2.81/1.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.46  tff(c_39, plain, (![A_20, C_21, B_22]: (r1_tarski(A_20, C_21) | ~r1_tarski(k2_xboole_0(A_20, B_22), C_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.46  tff(c_57, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(resolution, [status(thm)], [c_6, c_39])).
% 2.81/1.46  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.46  tff(c_68, plain, (![A_3, B_4, B_25]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_25)))), inference(resolution, [status(thm)], [c_57, c_8])).
% 2.81/1.46  tff(c_296, plain, (![B_47]: (r1_tarski('#skF_1', k2_xboole_0(k7_relat_1('#skF_2', k1_relat_1('#skF_1')), B_47)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_68])).
% 2.81/1.46  tff(c_309, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_37, c_296])).
% 2.81/1.46  tff(c_318, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_309])).
% 2.81/1.46  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_318])).
% 2.81/1.46  tff(c_321, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 2.81/1.46  tff(c_550, plain, (![C_61, B_62, A_63]: (r1_tarski(C_61, k7_relat_1(B_62, A_63)) | ~r1_tarski(C_61, B_62) | ~r1_tarski(k1_relat_1(C_61), A_63) | ~v1_relat_1(C_61) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.81/1.46  tff(c_917, plain, (![C_94, B_95]: (r1_tarski(C_94, k7_relat_1(B_95, k1_relat_1(C_94))) | ~r1_tarski(C_94, B_95) | ~v1_relat_1(C_94) | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_6, c_550])).
% 2.81/1.46  tff(c_322, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitRight, [status(thm)], [c_26])).
% 2.81/1.46  tff(c_941, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_917, c_322])).
% 2.81/1.46  tff(c_964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_321, c_941])).
% 2.81/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.46  
% 2.81/1.46  Inference rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Ref     : 0
% 2.81/1.46  #Sup     : 216
% 2.81/1.46  #Fact    : 0
% 2.81/1.46  #Define  : 0
% 2.81/1.46  #Split   : 2
% 2.81/1.46  #Chain   : 0
% 2.81/1.46  #Close   : 0
% 2.81/1.46  
% 2.81/1.46  Ordering : KBO
% 2.81/1.46  
% 2.81/1.46  Simplification rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Subsume      : 22
% 2.81/1.46  #Demod        : 109
% 2.81/1.46  #Tautology    : 102
% 2.81/1.46  #SimpNegUnit  : 1
% 2.81/1.46  #BackRed      : 0
% 2.81/1.46  
% 2.81/1.46  #Partial instantiations: 0
% 2.81/1.46  #Strategies tried      : 1
% 2.81/1.46  
% 2.81/1.46  Timing (in seconds)
% 2.81/1.46  ----------------------
% 2.81/1.46  Preprocessing        : 0.29
% 2.81/1.46  Parsing              : 0.16
% 2.81/1.46  CNF conversion       : 0.02
% 2.81/1.46  Main loop            : 0.34
% 2.81/1.46  Inferencing          : 0.13
% 2.81/1.46  Reduction            : 0.10
% 2.81/1.46  Demodulation         : 0.08
% 2.81/1.46  BG Simplification    : 0.02
% 2.81/1.46  Subsumption          : 0.07
% 2.81/1.46  Abstraction          : 0.02
% 2.81/1.46  MUC search           : 0.00
% 2.81/1.46  Cooper               : 0.00
% 2.81/1.47  Total                : 0.66
% 2.81/1.47  Index Insertion      : 0.00
% 2.81/1.47  Index Deletion       : 0.00
% 2.81/1.47  Index Matching       : 0.00
% 2.81/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
