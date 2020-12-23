%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:55 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  71 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k10_relat_1(C,A),k10_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t180_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

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

tff(c_16,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k10_relat_1(C_8,A_6),k10_relat_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_55,plain,(
    ! [B_25,A_26,C_27] :
      ( r1_tarski(k10_relat_1(B_25,A_26),k10_relat_1(C_27,A_26))
      | ~ r1_tarski(B_25,C_27)
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    ! [B_31,A_32,C_33] :
      ( k2_xboole_0(k10_relat_1(B_31,A_32),k10_relat_1(C_33,A_32)) = k10_relat_1(C_33,A_32)
      | ~ r1_tarski(B_31,C_33)
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_55,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_163,plain,(
    ! [B_49,A_50,C_51,C_52] :
      ( r1_tarski(k10_relat_1(B_49,A_50),C_51)
      | ~ r1_tarski(k10_relat_1(C_52,A_50),C_51)
      | ~ r1_tarski(B_49,C_52)
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2])).

tff(c_310,plain,(
    ! [B_72,A_73,C_74,B_75] :
      ( r1_tarski(k10_relat_1(B_72,A_73),k10_relat_1(C_74,B_75))
      | ~ r1_tarski(B_72,C_74)
      | ~ v1_relat_1(B_72)
      | ~ r1_tarski(A_73,B_75)
      | ~ v1_relat_1(C_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_163])).

tff(c_10,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_325,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_310,c_10])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12,c_18,c_14,c_325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.37  
% 2.24/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.37  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.24/1.37  
% 2.24/1.37  %Foreground sorts:
% 2.24/1.37  
% 2.24/1.37  
% 2.24/1.37  %Background operators:
% 2.24/1.37  
% 2.24/1.37  
% 2.24/1.37  %Foreground operators:
% 2.24/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.24/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.37  
% 2.24/1.38  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k10_relat_1(C, A), k10_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t180_relat_1)).
% 2.24/1.38  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 2.24/1.38  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t179_relat_1)).
% 2.24/1.38  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.24/1.38  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.24/1.38  tff(c_16, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.24/1.38  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.24/1.38  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.24/1.38  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.24/1.38  tff(c_6, plain, (![C_8, A_6, B_7]: (r1_tarski(k10_relat_1(C_8, A_6), k10_relat_1(C_8, B_7)) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.38  tff(c_55, plain, (![B_25, A_26, C_27]: (r1_tarski(k10_relat_1(B_25, A_26), k10_relat_1(C_27, A_26)) | ~r1_tarski(B_25, C_27) | ~v1_relat_1(C_27) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.24/1.38  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.38  tff(c_72, plain, (![B_31, A_32, C_33]: (k2_xboole_0(k10_relat_1(B_31, A_32), k10_relat_1(C_33, A_32))=k10_relat_1(C_33, A_32) | ~r1_tarski(B_31, C_33) | ~v1_relat_1(C_33) | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_55, c_4])).
% 2.24/1.38  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.38  tff(c_163, plain, (![B_49, A_50, C_51, C_52]: (r1_tarski(k10_relat_1(B_49, A_50), C_51) | ~r1_tarski(k10_relat_1(C_52, A_50), C_51) | ~r1_tarski(B_49, C_52) | ~v1_relat_1(C_52) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2])).
% 2.24/1.38  tff(c_310, plain, (![B_72, A_73, C_74, B_75]: (r1_tarski(k10_relat_1(B_72, A_73), k10_relat_1(C_74, B_75)) | ~r1_tarski(B_72, C_74) | ~v1_relat_1(B_72) | ~r1_tarski(A_73, B_75) | ~v1_relat_1(C_74))), inference(resolution, [status(thm)], [c_6, c_163])).
% 2.24/1.38  tff(c_10, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.24/1.38  tff(c_325, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_310, c_10])).
% 2.24/1.38  tff(c_338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_12, c_18, c_14, c_325])).
% 2.24/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.38  
% 2.24/1.38  Inference rules
% 2.24/1.38  ----------------------
% 2.24/1.38  #Ref     : 0
% 2.24/1.38  #Sup     : 87
% 2.24/1.38  #Fact    : 0
% 2.24/1.38  #Define  : 0
% 2.24/1.38  #Split   : 3
% 2.24/1.38  #Chain   : 0
% 2.24/1.38  #Close   : 0
% 2.24/1.38  
% 2.24/1.38  Ordering : KBO
% 2.24/1.38  
% 2.24/1.38  Simplification rules
% 2.24/1.38  ----------------------
% 2.24/1.38  #Subsume      : 9
% 2.24/1.38  #Demod        : 4
% 2.24/1.38  #Tautology    : 20
% 2.24/1.38  #SimpNegUnit  : 0
% 2.24/1.38  #BackRed      : 0
% 2.24/1.38  
% 2.24/1.38  #Partial instantiations: 0
% 2.24/1.38  #Strategies tried      : 1
% 2.24/1.38  
% 2.24/1.38  Timing (in seconds)
% 2.24/1.38  ----------------------
% 2.56/1.39  Preprocessing        : 0.29
% 2.56/1.39  Parsing              : 0.16
% 2.56/1.39  CNF conversion       : 0.02
% 2.56/1.39  Main loop            : 0.29
% 2.56/1.39  Inferencing          : 0.11
% 2.56/1.39  Reduction            : 0.06
% 2.56/1.39  Demodulation         : 0.04
% 2.56/1.39  BG Simplification    : 0.02
% 2.56/1.39  Subsumption          : 0.08
% 2.56/1.39  Abstraction          : 0.01
% 2.56/1.39  MUC search           : 0.00
% 2.56/1.39  Cooper               : 0.00
% 2.56/1.39  Total                : 0.60
% 2.56/1.39  Index Insertion      : 0.00
% 2.56/1.39  Index Deletion       : 0.00
% 2.56/1.39  Index Matching       : 0.00
% 2.56/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
