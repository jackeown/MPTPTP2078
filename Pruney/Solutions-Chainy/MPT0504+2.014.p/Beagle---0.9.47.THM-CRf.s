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
% DateTime   : Thu Dec  3 09:59:50 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  30 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_27,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_27])).

tff(c_40,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_40])).

tff(c_61,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_66,plain,(
    ! [C_16,A_17,B_18] :
      ( k7_relat_1(k7_relat_1(C_16,A_17),B_18) = k7_relat_1(C_16,k3_xboole_0(A_17,B_18))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_12])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_61,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:00:35 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.16  
% 1.61/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.17  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.61/1.17  
% 1.61/1.17  %Foreground sorts:
% 1.61/1.17  
% 1.61/1.17  
% 1.61/1.17  %Background operators:
% 1.61/1.17  
% 1.61/1.17  
% 1.61/1.17  %Foreground operators:
% 1.61/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.61/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.61/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.61/1.17  
% 1.61/1.18  tff(f_44, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.61/1.18  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.61/1.18  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.61/1.18  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.61/1.18  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.61/1.18  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.61/1.18  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.18  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.61/1.18  tff(c_27, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.18  tff(c_35, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_27])).
% 1.61/1.18  tff(c_40, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.18  tff(c_55, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35, c_40])).
% 1.61/1.18  tff(c_61, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_55])).
% 1.61/1.18  tff(c_66, plain, (![C_16, A_17, B_18]: (k7_relat_1(k7_relat_1(C_16, A_17), B_18)=k7_relat_1(C_16, k3_xboole_0(A_17, B_18)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.61/1.18  tff(c_12, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.61/1.18  tff(c_75, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_66, c_12])).
% 1.61/1.18  tff(c_85, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_61, c_75])).
% 1.61/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.18  
% 1.61/1.18  Inference rules
% 1.61/1.18  ----------------------
% 1.61/1.18  #Ref     : 0
% 1.61/1.18  #Sup     : 19
% 1.61/1.18  #Fact    : 0
% 1.61/1.18  #Define  : 0
% 1.61/1.18  #Split   : 0
% 1.61/1.18  #Chain   : 0
% 1.61/1.18  #Close   : 0
% 1.61/1.18  
% 1.61/1.18  Ordering : KBO
% 1.61/1.18  
% 1.61/1.18  Simplification rules
% 1.61/1.18  ----------------------
% 1.61/1.18  #Subsume      : 0
% 1.61/1.18  #Demod        : 3
% 1.61/1.18  #Tautology    : 10
% 1.61/1.18  #SimpNegUnit  : 0
% 1.61/1.18  #BackRed      : 0
% 1.61/1.18  
% 1.61/1.18  #Partial instantiations: 0
% 1.61/1.18  #Strategies tried      : 1
% 1.61/1.18  
% 1.61/1.18  Timing (in seconds)
% 1.61/1.18  ----------------------
% 1.61/1.18  Preprocessing        : 0.28
% 1.79/1.18  Parsing              : 0.15
% 1.79/1.18  CNF conversion       : 0.02
% 1.79/1.18  Main loop            : 0.10
% 1.79/1.18  Inferencing          : 0.05
% 1.79/1.18  Reduction            : 0.03
% 1.79/1.18  Demodulation         : 0.02
% 1.79/1.18  BG Simplification    : 0.01
% 1.79/1.18  Subsumption          : 0.01
% 1.79/1.18  Abstraction          : 0.01
% 1.79/1.18  MUC search           : 0.00
% 1.79/1.18  Cooper               : 0.00
% 1.79/1.18  Total                : 0.41
% 1.79/1.18  Index Insertion      : 0.00
% 1.79/1.18  Index Deletion       : 0.00
% 1.79/1.18  Index Matching       : 0.00
% 1.79/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
