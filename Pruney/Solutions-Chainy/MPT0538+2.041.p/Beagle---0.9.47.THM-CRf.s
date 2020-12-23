%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:28 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_49,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(k1_tarski(A_39),B_40) = B_40
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),B_7) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_61,plain,(
    ! [B_41,A_42] :
      ( k1_xboole_0 != B_41
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_10])).

tff(c_66,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_61])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    ! [A_44,B_45] :
      ( k8_relat_1(A_44,B_45) = B_45
      | ~ r1_tarski(k2_relat_1(B_45),A_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,(
    ! [A_44] :
      ( k8_relat_1(A_44,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_68])).

tff(c_79,plain,(
    ! [A_46] :
      ( k8_relat_1(A_46,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_75])).

tff(c_83,plain,(
    ! [B_2] :
      ( k8_relat_1(B_2,k1_xboole_0) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_86,plain,(
    ! [B_2] : k8_relat_1(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_83])).

tff(c_24,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.14  
% 1.61/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.14  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.73/1.14  
% 1.73/1.14  %Foreground sorts:
% 1.73/1.14  
% 1.73/1.14  
% 1.73/1.14  %Background operators:
% 1.73/1.14  
% 1.73/1.14  
% 1.73/1.14  %Foreground operators:
% 1.73/1.14  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.73/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.73/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.73/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.73/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.73/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.14  
% 1.73/1.15  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.73/1.15  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.73/1.15  tff(f_48, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.73/1.15  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.73/1.15  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.73/1.15  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.73/1.15  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 1.73/1.15  tff(f_60, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.73/1.15  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.15  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.15  tff(c_16, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.73/1.15  tff(c_49, plain, (![A_39, B_40]: (k2_xboole_0(k1_tarski(A_39), B_40)=B_40 | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.15  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.73/1.15  tff(c_61, plain, (![B_41, A_42]: (k1_xboole_0!=B_41 | ~r2_hidden(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_49, c_10])).
% 1.73/1.15  tff(c_66, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_61])).
% 1.73/1.15  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.73/1.15  tff(c_68, plain, (![A_44, B_45]: (k8_relat_1(A_44, B_45)=B_45 | ~r1_tarski(k2_relat_1(B_45), A_44) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.15  tff(c_75, plain, (![A_44]: (k8_relat_1(A_44, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_44) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_68])).
% 1.73/1.15  tff(c_79, plain, (![A_46]: (k8_relat_1(A_46, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_75])).
% 1.73/1.15  tff(c_83, plain, (![B_2]: (k8_relat_1(B_2, k1_xboole_0)=k1_xboole_0 | k4_xboole_0(k1_xboole_0, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_79])).
% 1.73/1.15  tff(c_86, plain, (![B_2]: (k8_relat_1(B_2, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_83])).
% 1.73/1.15  tff(c_24, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.73/1.15  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_24])).
% 1.73/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.15  
% 1.73/1.15  Inference rules
% 1.73/1.15  ----------------------
% 1.73/1.15  #Ref     : 0
% 1.73/1.15  #Sup     : 14
% 1.73/1.15  #Fact    : 0
% 1.73/1.15  #Define  : 0
% 1.73/1.15  #Split   : 0
% 1.73/1.15  #Chain   : 0
% 1.73/1.15  #Close   : 0
% 1.73/1.15  
% 1.73/1.15  Ordering : KBO
% 1.73/1.15  
% 1.73/1.15  Simplification rules
% 1.73/1.15  ----------------------
% 1.73/1.15  #Subsume      : 0
% 1.73/1.15  #Demod        : 4
% 1.73/1.15  #Tautology    : 10
% 1.73/1.15  #SimpNegUnit  : 0
% 1.73/1.15  #BackRed      : 1
% 1.73/1.15  
% 1.73/1.15  #Partial instantiations: 0
% 1.73/1.15  #Strategies tried      : 1
% 1.73/1.15  
% 1.73/1.15  Timing (in seconds)
% 1.73/1.15  ----------------------
% 1.73/1.15  Preprocessing        : 0.26
% 1.73/1.15  Parsing              : 0.15
% 1.73/1.15  CNF conversion       : 0.02
% 1.73/1.15  Main loop            : 0.11
% 1.73/1.15  Inferencing          : 0.05
% 1.73/1.15  Reduction            : 0.03
% 1.73/1.15  Demodulation         : 0.02
% 1.73/1.15  BG Simplification    : 0.01
% 1.73/1.16  Subsumption          : 0.01
% 1.73/1.16  Abstraction          : 0.00
% 1.73/1.16  MUC search           : 0.00
% 1.73/1.16  Cooper               : 0.00
% 1.73/1.16  Total                : 0.39
% 1.73/1.16  Index Insertion      : 0.00
% 1.73/1.16  Index Deletion       : 0.00
% 1.73/1.16  Index Matching       : 0.00
% 1.73/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
