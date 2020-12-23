%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:37 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  71 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_22])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_65,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_65])).

tff(c_106,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_30,B_31)),k3_xboole_0(k1_relat_1(A_30),k1_relat_1(B_31)))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_115,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0)
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_106])).

tff(c_118,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_115])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_122,plain,(
    k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_118,c_8])).

tff(c_10,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,(
    k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_10])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k3_xboole_0(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_158,plain,(
    ! [A_32,B_33] :
      ( k1_relat_1(k3_xboole_0(A_32,B_33)) != k1_xboole_0
      | k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ v1_relat_1(A_32) ) ),
    inference(resolution,[status(thm)],[c_14,c_50])).

tff(c_161,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_158])).

tff(c_167,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_161])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.29  
% 1.81/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.29  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.81/1.29  
% 1.81/1.29  %Foreground sorts:
% 1.81/1.29  
% 1.81/1.29  
% 1.81/1.29  %Background operators:
% 1.81/1.29  
% 1.81/1.29  
% 1.81/1.29  %Foreground operators:
% 1.81/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.81/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.81/1.29  
% 1.81/1.30  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.81/1.30  tff(f_66, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 1.81/1.30  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relat_1)).
% 1.81/1.30  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.81/1.30  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.81/1.30  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.81/1.30  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.81/1.30  tff(c_40, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k3_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.30  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.81/1.30  tff(c_44, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_22])).
% 1.81/1.30  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.81/1.30  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.81/1.30  tff(c_24, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.81/1.30  tff(c_65, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.30  tff(c_73, plain, (k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_65])).
% 1.81/1.30  tff(c_106, plain, (![A_30, B_31]: (r1_tarski(k1_relat_1(k3_xboole_0(A_30, B_31)), k3_xboole_0(k1_relat_1(A_30), k1_relat_1(B_31))) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.30  tff(c_115, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_73, c_106])).
% 1.81/1.30  tff(c_118, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_115])).
% 1.81/1.30  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.30  tff(c_122, plain, (k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_118, c_8])).
% 1.81/1.30  tff(c_10, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.30  tff(c_126, plain, (k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_122, c_10])).
% 1.81/1.30  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k3_xboole_0(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.81/1.30  tff(c_50, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.81/1.30  tff(c_158, plain, (![A_32, B_33]: (k1_relat_1(k3_xboole_0(A_32, B_33))!=k1_xboole_0 | k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~v1_relat_1(A_32))), inference(resolution, [status(thm)], [c_14, c_50])).
% 1.81/1.30  tff(c_161, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_126, c_158])).
% 1.81/1.30  tff(c_167, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_161])).
% 1.81/1.30  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_167])).
% 1.81/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.30  
% 1.81/1.30  Inference rules
% 1.81/1.30  ----------------------
% 1.81/1.30  #Ref     : 0
% 1.81/1.30  #Sup     : 33
% 1.81/1.30  #Fact    : 0
% 1.81/1.30  #Define  : 0
% 1.81/1.30  #Split   : 5
% 1.81/1.30  #Chain   : 0
% 1.81/1.30  #Close   : 0
% 1.81/1.30  
% 1.81/1.30  Ordering : KBO
% 1.81/1.30  
% 1.81/1.30  Simplification rules
% 1.81/1.30  ----------------------
% 1.81/1.30  #Subsume      : 1
% 1.81/1.30  #Demod        : 12
% 1.81/1.30  #Tautology    : 16
% 1.81/1.30  #SimpNegUnit  : 1
% 1.81/1.30  #BackRed      : 2
% 1.81/1.30  
% 1.81/1.30  #Partial instantiations: 0
% 1.81/1.30  #Strategies tried      : 1
% 1.81/1.30  
% 1.81/1.30  Timing (in seconds)
% 1.81/1.30  ----------------------
% 1.81/1.31  Preprocessing        : 0.27
% 1.81/1.31  Parsing              : 0.15
% 1.81/1.31  CNF conversion       : 0.02
% 1.81/1.31  Main loop            : 0.15
% 1.81/1.31  Inferencing          : 0.06
% 1.81/1.31  Reduction            : 0.04
% 1.81/1.31  Demodulation         : 0.03
% 1.81/1.31  BG Simplification    : 0.01
% 1.81/1.31  Subsumption          : 0.02
% 1.81/1.31  Abstraction          : 0.01
% 1.81/1.31  MUC search           : 0.00
% 1.81/1.31  Cooper               : 0.00
% 1.81/1.31  Total                : 0.45
% 1.81/1.31  Index Insertion      : 0.00
% 1.81/1.31  Index Deletion       : 0.00
% 1.81/1.31  Index Matching       : 0.00
% 1.81/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
