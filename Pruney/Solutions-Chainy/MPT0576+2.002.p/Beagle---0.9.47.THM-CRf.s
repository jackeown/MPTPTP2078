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
% DateTime   : Thu Dec  3 10:01:54 EST 2020

% Result     : Theorem 11.37s
% Output     : CNFRefutation 11.37s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  76 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k10_relat_1(C,A),k10_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t180_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [B_20,A_19,C_22] :
      ( r1_tarski(k10_relat_1(B_20,A_19),k10_relat_1(C_22,A_19))
      | ~ r1_tarski(B_20,C_22)
      | ~ v1_relat_1(C_22)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_86,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_110,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_86])).

tff(c_20,plain,(
    ! [C_18,A_16,B_17] :
      ( k2_xboole_0(k10_relat_1(C_18,A_16),k10_relat_1(C_18,B_17)) = k10_relat_1(C_18,k2_xboole_0(A_16,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_279,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_905,plain,(
    ! [A_79,A_80,B_81] :
      ( r1_tarski(A_79,k2_xboole_0(A_80,B_81))
      | ~ r1_tarski(A_79,A_80) ) ),
    inference(resolution,[status(thm)],[c_18,c_279])).

tff(c_8319,plain,(
    ! [A_251,C_252,A_253,B_254] :
      ( r1_tarski(A_251,k10_relat_1(C_252,k2_xboole_0(A_253,B_254)))
      | ~ r1_tarski(A_251,k10_relat_1(C_252,A_253))
      | ~ v1_relat_1(C_252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_905])).

tff(c_24706,plain,(
    ! [A_440,C_441] :
      ( r1_tarski(A_440,k10_relat_1(C_441,'#skF_2'))
      | ~ r1_tarski(A_440,k10_relat_1(C_441,'#skF_1'))
      | ~ v1_relat_1(C_441) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_8319])).

tff(c_24,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24801,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24706,c_24])).

tff(c_24833,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24801])).

tff(c_24836,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_24833])).

tff(c_24840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_24836])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.37/4.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.37/4.85  
% 11.37/4.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.37/4.85  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.37/4.85  
% 11.37/4.85  %Foreground sorts:
% 11.37/4.85  
% 11.37/4.85  
% 11.37/4.85  %Background operators:
% 11.37/4.85  
% 11.37/4.85  
% 11.37/4.85  %Foreground operators:
% 11.37/4.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.37/4.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.37/4.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.37/4.85  tff('#skF_2', type, '#skF_2': $i).
% 11.37/4.85  tff('#skF_3', type, '#skF_3': $i).
% 11.37/4.85  tff('#skF_1', type, '#skF_1': $i).
% 11.37/4.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.37/4.85  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.37/4.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.37/4.85  tff('#skF_4', type, '#skF_4': $i).
% 11.37/4.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.37/4.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.37/4.85  
% 11.37/4.86  tff(f_74, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k10_relat_1(C, A), k10_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t180_relat_1)).
% 11.37/4.86  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t179_relat_1)).
% 11.37/4.86  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.37/4.86  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 11.37/4.86  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.37/4.86  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.37/4.86  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.37/4.86  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.37/4.86  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.37/4.86  tff(c_22, plain, (![B_20, A_19, C_22]: (r1_tarski(k10_relat_1(B_20, A_19), k10_relat_1(C_22, A_19)) | ~r1_tarski(B_20, C_22) | ~v1_relat_1(C_22) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.37/4.86  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.37/4.86  tff(c_86, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.37/4.86  tff(c_110, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_86])).
% 11.37/4.86  tff(c_20, plain, (![C_18, A_16, B_17]: (k2_xboole_0(k10_relat_1(C_18, A_16), k10_relat_1(C_18, B_17))=k10_relat_1(C_18, k2_xboole_0(A_16, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.37/4.86  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.37/4.86  tff(c_279, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.37/4.86  tff(c_905, plain, (![A_79, A_80, B_81]: (r1_tarski(A_79, k2_xboole_0(A_80, B_81)) | ~r1_tarski(A_79, A_80))), inference(resolution, [status(thm)], [c_18, c_279])).
% 11.37/4.86  tff(c_8319, plain, (![A_251, C_252, A_253, B_254]: (r1_tarski(A_251, k10_relat_1(C_252, k2_xboole_0(A_253, B_254))) | ~r1_tarski(A_251, k10_relat_1(C_252, A_253)) | ~v1_relat_1(C_252))), inference(superposition, [status(thm), theory('equality')], [c_20, c_905])).
% 11.37/4.86  tff(c_24706, plain, (![A_440, C_441]: (r1_tarski(A_440, k10_relat_1(C_441, '#skF_2')) | ~r1_tarski(A_440, k10_relat_1(C_441, '#skF_1')) | ~v1_relat_1(C_441))), inference(superposition, [status(thm), theory('equality')], [c_110, c_8319])).
% 11.37/4.86  tff(c_24, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.37/4.86  tff(c_24801, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_1')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24706, c_24])).
% 11.37/4.86  tff(c_24833, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24801])).
% 11.37/4.86  tff(c_24836, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_24833])).
% 11.37/4.86  tff(c_24840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_24836])).
% 11.37/4.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.37/4.86  
% 11.37/4.86  Inference rules
% 11.37/4.86  ----------------------
% 11.37/4.86  #Ref     : 0
% 11.37/4.86  #Sup     : 6358
% 11.37/4.86  #Fact    : 0
% 11.37/4.86  #Define  : 0
% 11.37/4.86  #Split   : 11
% 11.37/4.86  #Chain   : 0
% 11.37/4.86  #Close   : 0
% 11.37/4.86  
% 11.37/4.86  Ordering : KBO
% 11.37/4.86  
% 11.37/4.86  Simplification rules
% 11.37/4.86  ----------------------
% 11.37/4.86  #Subsume      : 1543
% 11.37/4.86  #Demod        : 5577
% 11.37/4.86  #Tautology    : 2409
% 11.37/4.86  #SimpNegUnit  : 0
% 11.37/4.86  #BackRed      : 0
% 11.37/4.86  
% 11.37/4.86  #Partial instantiations: 0
% 11.37/4.86  #Strategies tried      : 1
% 11.37/4.86  
% 11.37/4.86  Timing (in seconds)
% 11.37/4.86  ----------------------
% 11.37/4.86  Preprocessing        : 0.28
% 11.37/4.86  Parsing              : 0.15
% 11.37/4.86  CNF conversion       : 0.02
% 11.37/4.86  Main loop            : 3.81
% 11.37/4.86  Inferencing          : 0.68
% 11.37/4.86  Reduction            : 1.95
% 11.37/4.86  Demodulation         : 1.70
% 11.37/4.86  BG Simplification    : 0.08
% 11.37/4.86  Subsumption          : 0.91
% 11.37/4.86  Abstraction          : 0.12
% 11.37/4.86  MUC search           : 0.00
% 11.37/4.86  Cooper               : 0.00
% 11.37/4.86  Total                : 4.11
% 11.37/4.86  Index Insertion      : 0.00
% 11.37/4.86  Index Deletion       : 0.00
% 11.37/4.86  Index Matching       : 0.00
% 11.37/4.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
