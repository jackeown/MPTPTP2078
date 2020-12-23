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
% DateTime   : Thu Dec  3 10:01:43 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_183,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(k2_relat_1(B_33),A_34)
      | k10_relat_1(B_33,A_34) != k1_xboole_0
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_526,plain,(
    ! [B_45,A_46] :
      ( k3_xboole_0(k2_relat_1(B_45),A_46) = k1_xboole_0
      | k10_relat_1(B_45,A_46) != k1_xboole_0
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_183,c_4])).

tff(c_601,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,k2_relat_1(B_48)) = k1_xboole_0
      | k10_relat_1(B_48,A_47) != k1_xboole_0
      | ~ v1_relat_1(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_526])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    k4_xboole_0('#skF_1',k2_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_76])).

tff(c_104,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_119,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_104])).

tff(c_125,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_119])).

tff(c_633,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_125])).

tff(c_667,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_633])).

tff(c_669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_667])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.34  
% 2.48/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.34  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.48/1.34  
% 2.48/1.34  %Foreground sorts:
% 2.48/1.34  
% 2.48/1.34  
% 2.48/1.34  %Background operators:
% 2.48/1.34  
% 2.48/1.34  
% 2.48/1.34  %Foreground operators:
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.48/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.48/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.48/1.34  
% 2.48/1.35  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.48/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.48/1.35  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.48/1.35  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.48/1.35  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.48/1.35  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.48/1.35  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.48/1.35  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.48/1.35  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.48/1.35  tff(c_22, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.48/1.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.35  tff(c_183, plain, (![B_33, A_34]: (r1_xboole_0(k2_relat_1(B_33), A_34) | k10_relat_1(B_33, A_34)!=k1_xboole_0 | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.35  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.35  tff(c_526, plain, (![B_45, A_46]: (k3_xboole_0(k2_relat_1(B_45), A_46)=k1_xboole_0 | k10_relat_1(B_45, A_46)!=k1_xboole_0 | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_183, c_4])).
% 2.48/1.35  tff(c_601, plain, (![A_47, B_48]: (k3_xboole_0(A_47, k2_relat_1(B_48))=k1_xboole_0 | k10_relat_1(B_48, A_47)!=k1_xboole_0 | ~v1_relat_1(B_48))), inference(superposition, [status(thm), theory('equality')], [c_2, c_526])).
% 2.48/1.35  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.48/1.35  tff(c_24, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.48/1.35  tff(c_76, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.35  tff(c_80, plain, (k4_xboole_0('#skF_1', k2_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_76])).
% 2.48/1.35  tff(c_104, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.48/1.35  tff(c_119, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_104])).
% 2.48/1.35  tff(c_125, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_119])).
% 2.48/1.35  tff(c_633, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_601, c_125])).
% 2.48/1.35  tff(c_667, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_633])).
% 2.48/1.35  tff(c_669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_667])).
% 2.48/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.35  
% 2.48/1.35  Inference rules
% 2.48/1.35  ----------------------
% 2.48/1.35  #Ref     : 0
% 2.48/1.35  #Sup     : 154
% 2.48/1.35  #Fact    : 0
% 2.48/1.35  #Define  : 0
% 2.48/1.35  #Split   : 0
% 2.48/1.35  #Chain   : 0
% 2.48/1.35  #Close   : 0
% 2.48/1.35  
% 2.48/1.35  Ordering : KBO
% 2.48/1.35  
% 2.48/1.35  Simplification rules
% 2.48/1.35  ----------------------
% 2.48/1.35  #Subsume      : 12
% 2.48/1.35  #Demod        : 90
% 2.48/1.35  #Tautology    : 90
% 2.48/1.35  #SimpNegUnit  : 1
% 2.48/1.35  #BackRed      : 0
% 2.48/1.35  
% 2.48/1.35  #Partial instantiations: 0
% 2.48/1.35  #Strategies tried      : 1
% 2.48/1.35  
% 2.48/1.35  Timing (in seconds)
% 2.48/1.35  ----------------------
% 2.48/1.36  Preprocessing        : 0.29
% 2.48/1.36  Parsing              : 0.16
% 2.48/1.36  CNF conversion       : 0.02
% 2.48/1.36  Main loop            : 0.30
% 2.48/1.36  Inferencing          : 0.11
% 2.48/1.36  Reduction            : 0.12
% 2.48/1.36  Demodulation         : 0.09
% 2.48/1.36  BG Simplification    : 0.01
% 2.48/1.36  Subsumption          : 0.05
% 2.48/1.36  Abstraction          : 0.01
% 2.48/1.36  MUC search           : 0.00
% 2.48/1.36  Cooper               : 0.00
% 2.48/1.36  Total                : 0.62
% 2.48/1.36  Index Insertion      : 0.00
% 2.48/1.36  Index Deletion       : 0.00
% 2.48/1.36  Index Matching       : 0.00
% 2.48/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
