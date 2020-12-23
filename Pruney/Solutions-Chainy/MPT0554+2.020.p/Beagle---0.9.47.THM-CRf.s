%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:05 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  29 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_14])).

tff(c_56,plain,(
    ! [C_14,A_15,B_16] :
      ( k2_xboole_0(k9_relat_1(C_14,A_15),k9_relat_1(C_14,B_16)) = k9_relat_1(C_14,k2_xboole_0(A_15,B_16))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [C_17,A_18,B_19] :
      ( r1_tarski(k9_relat_1(C_17,A_18),k9_relat_1(C_17,k2_xboole_0(A_18,B_19)))
      | ~ v1_relat_1(C_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4])).

tff(c_85,plain,(
    ! [C_20] :
      ( r1_tarski(k9_relat_1(C_20,'#skF_1'),k9_relat_1(C_20,'#skF_2'))
      | ~ v1_relat_1(C_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_71])).

tff(c_8,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:23:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.18  
% 1.72/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.18  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.72/1.18  
% 1.72/1.18  %Foreground sorts:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Background operators:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Foreground operators:
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.72/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.18  
% 1.72/1.19  tff(f_42, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 1.72/1.19  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.72/1.19  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 1.72/1.19  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.72/1.19  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.72/1.19  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.72/1.19  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.72/1.19  tff(c_22, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_10, c_14])).
% 1.72/1.19  tff(c_56, plain, (![C_14, A_15, B_16]: (k2_xboole_0(k9_relat_1(C_14, A_15), k9_relat_1(C_14, B_16))=k9_relat_1(C_14, k2_xboole_0(A_15, B_16)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.19  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.19  tff(c_71, plain, (![C_17, A_18, B_19]: (r1_tarski(k9_relat_1(C_17, A_18), k9_relat_1(C_17, k2_xboole_0(A_18, B_19))) | ~v1_relat_1(C_17))), inference(superposition, [status(thm), theory('equality')], [c_56, c_4])).
% 1.72/1.19  tff(c_85, plain, (![C_20]: (r1_tarski(k9_relat_1(C_20, '#skF_1'), k9_relat_1(C_20, '#skF_2')) | ~v1_relat_1(C_20))), inference(superposition, [status(thm), theory('equality')], [c_22, c_71])).
% 1.72/1.19  tff(c_8, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.72/1.19  tff(c_88, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_85, c_8])).
% 1.72/1.19  tff(c_95, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_88])).
% 1.72/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.19  
% 1.72/1.19  Inference rules
% 1.72/1.19  ----------------------
% 1.72/1.19  #Ref     : 0
% 1.72/1.19  #Sup     : 21
% 1.72/1.19  #Fact    : 0
% 1.72/1.19  #Define  : 0
% 1.72/1.19  #Split   : 0
% 1.72/1.19  #Chain   : 0
% 1.72/1.19  #Close   : 0
% 1.72/1.19  
% 1.72/1.19  Ordering : KBO
% 1.72/1.19  
% 1.72/1.19  Simplification rules
% 1.72/1.19  ----------------------
% 1.72/1.19  #Subsume      : 1
% 1.72/1.19  #Demod        : 9
% 1.72/1.19  #Tautology    : 11
% 1.72/1.19  #SimpNegUnit  : 0
% 1.72/1.19  #BackRed      : 0
% 1.72/1.19  
% 1.72/1.19  #Partial instantiations: 0
% 1.72/1.19  #Strategies tried      : 1
% 1.72/1.19  
% 1.72/1.19  Timing (in seconds)
% 1.72/1.19  ----------------------
% 1.72/1.20  Preprocessing        : 0.23
% 1.72/1.20  Parsing              : 0.12
% 1.72/1.20  CNF conversion       : 0.01
% 1.72/1.20  Main loop            : 0.13
% 1.72/1.20  Inferencing          : 0.06
% 1.72/1.20  Reduction            : 0.03
% 1.72/1.20  Demodulation         : 0.03
% 1.72/1.20  BG Simplification    : 0.01
% 1.72/1.20  Subsumption          : 0.01
% 1.72/1.20  Abstraction          : 0.01
% 1.72/1.20  MUC search           : 0.00
% 1.72/1.20  Cooper               : 0.00
% 1.72/1.20  Total                : 0.38
% 1.72/1.20  Index Insertion      : 0.00
% 1.72/1.20  Index Deletion       : 0.00
% 1.72/1.20  Index Matching       : 0.00
% 1.72/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
