%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:54 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  40 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_26])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_31,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_31])).

tff(c_160,plain,(
    ! [C_31,A_32,B_33] :
      ( k2_xboole_0(k10_relat_1(C_31,A_32),k10_relat_1(C_31,B_33)) = k10_relat_1(C_31,k2_xboole_0(A_32,B_33))
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_388,plain,(
    ! [C_53,A_54,C_55,B_56] :
      ( r1_tarski(k10_relat_1(C_53,A_54),C_55)
      | ~ r1_tarski(k10_relat_1(C_53,k2_xboole_0(A_54,B_56)),C_55)
      | ~ v1_relat_1(C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_2])).

tff(c_527,plain,(
    ! [C_63,C_64] :
      ( r1_tarski(k10_relat_1(C_63,'#skF_1'),C_64)
      | ~ r1_tarski(k10_relat_1(C_63,'#skF_2'),C_64)
      | ~ v1_relat_1(C_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_388])).

tff(c_692,plain,(
    ! [C_72] :
      ( r1_tarski(k10_relat_1(C_72,'#skF_1'),k10_relat_1(C_72,'#skF_2'))
      | ~ v1_relat_1(C_72) ) ),
    inference(resolution,[status(thm)],[c_29,c_527])).

tff(c_12,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_695,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_692,c_12])).

tff(c_702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_695])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:17:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.16/1.29  
% 2.16/1.29  %Foreground sorts:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Background operators:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Foreground operators:
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.16/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.29  
% 2.16/1.30  tff(f_48, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 2.16/1.30  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.16/1.30  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.16/1.30  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.16/1.30  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 2.16/1.30  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.16/1.30  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.30  tff(c_8, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.30  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.30  tff(c_29, plain, (![A_8]: (r1_tarski(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_26])).
% 2.16/1.30  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.30  tff(c_31, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.30  tff(c_43, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_31])).
% 2.16/1.30  tff(c_160, plain, (![C_31, A_32, B_33]: (k2_xboole_0(k10_relat_1(C_31, A_32), k10_relat_1(C_31, B_33))=k10_relat_1(C_31, k2_xboole_0(A_32, B_33)) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.30  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.30  tff(c_388, plain, (![C_53, A_54, C_55, B_56]: (r1_tarski(k10_relat_1(C_53, A_54), C_55) | ~r1_tarski(k10_relat_1(C_53, k2_xboole_0(A_54, B_56)), C_55) | ~v1_relat_1(C_53))), inference(superposition, [status(thm), theory('equality')], [c_160, c_2])).
% 2.16/1.30  tff(c_527, plain, (![C_63, C_64]: (r1_tarski(k10_relat_1(C_63, '#skF_1'), C_64) | ~r1_tarski(k10_relat_1(C_63, '#skF_2'), C_64) | ~v1_relat_1(C_63))), inference(superposition, [status(thm), theory('equality')], [c_43, c_388])).
% 2.16/1.30  tff(c_692, plain, (![C_72]: (r1_tarski(k10_relat_1(C_72, '#skF_1'), k10_relat_1(C_72, '#skF_2')) | ~v1_relat_1(C_72))), inference(resolution, [status(thm)], [c_29, c_527])).
% 2.16/1.30  tff(c_12, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.30  tff(c_695, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_692, c_12])).
% 2.16/1.30  tff(c_702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_695])).
% 2.16/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  Inference rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Ref     : 0
% 2.16/1.30  #Sup     : 159
% 2.16/1.30  #Fact    : 0
% 2.16/1.30  #Define  : 0
% 2.16/1.30  #Split   : 0
% 2.16/1.30  #Chain   : 0
% 2.16/1.30  #Close   : 0
% 2.16/1.30  
% 2.16/1.30  Ordering : KBO
% 2.16/1.30  
% 2.16/1.30  Simplification rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Subsume      : 7
% 2.16/1.30  #Demod        : 74
% 2.16/1.30  #Tautology    : 92
% 2.16/1.30  #SimpNegUnit  : 0
% 2.16/1.30  #BackRed      : 0
% 2.16/1.30  
% 2.16/1.30  #Partial instantiations: 0
% 2.16/1.30  #Strategies tried      : 1
% 2.16/1.30  
% 2.47/1.30  Timing (in seconds)
% 2.47/1.30  ----------------------
% 2.47/1.30  Preprocessing        : 0.25
% 2.47/1.30  Parsing              : 0.14
% 2.47/1.30  CNF conversion       : 0.02
% 2.47/1.30  Main loop            : 0.30
% 2.47/1.30  Inferencing          : 0.13
% 2.47/1.30  Reduction            : 0.09
% 2.47/1.30  Demodulation         : 0.07
% 2.47/1.30  BG Simplification    : 0.01
% 2.47/1.30  Subsumption          : 0.05
% 2.47/1.30  Abstraction          : 0.01
% 2.47/1.30  MUC search           : 0.00
% 2.47/1.30  Cooper               : 0.00
% 2.47/1.30  Total                : 0.57
% 2.47/1.30  Index Insertion      : 0.00
% 2.47/1.30  Index Deletion       : 0.00
% 2.47/1.30  Index Matching       : 0.00
% 2.47/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
