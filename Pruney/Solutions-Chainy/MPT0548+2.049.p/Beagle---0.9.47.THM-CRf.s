%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:41 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  77 expanded)
%              Number of equality atoms :   23 (  50 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53,plain,(
    ! [A_34] :
      ( k9_relat_1(A_34,k1_relat_1(A_34)) = k2_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_53])).

tff(c_65,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_62])).

tff(c_66,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_16,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [B_38,A_39] :
      ( ~ r2_hidden(B_38,A_39)
      | k4_xboole_0(A_39,k1_tarski(B_38)) != A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_135,plain,(
    ! [B_42] : ~ r2_hidden(B_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_103])).

tff(c_139,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_135])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_139])).

tff(c_145,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_144,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_150,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_160,plain,(
    ! [B_44] : k3_xboole_0(k1_xboole_0,B_44) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_4])).

tff(c_218,plain,(
    ! [B_50,A_51] :
      ( k9_relat_1(B_50,k3_xboole_0(k1_relat_1(B_50),A_51)) = k9_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_227,plain,(
    ! [A_51] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_51)) = k9_relat_1(k1_xboole_0,A_51)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_218])).

tff(c_231,plain,(
    ! [A_51] : k9_relat_1(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_144,c_160,c_227])).

tff(c_26,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.15  
% 1.82/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.16  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.82/1.16  
% 1.82/1.16  %Foreground sorts:
% 1.82/1.16  
% 1.82/1.16  
% 1.82/1.16  %Background operators:
% 1.82/1.16  
% 1.82/1.16  
% 1.82/1.16  %Foreground operators:
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.82/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.82/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.82/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.82/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.82/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.82/1.16  
% 1.82/1.17  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.82/1.17  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 1.82/1.17  tff(f_46, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.82/1.17  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.82/1.17  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.82/1.17  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.82/1.17  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 1.82/1.17  tff(f_60, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.82/1.17  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.17  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.17  tff(c_53, plain, (![A_34]: (k9_relat_1(A_34, k1_relat_1(A_34))=k2_relat_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.82/1.17  tff(c_62, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_53])).
% 1.82/1.17  tff(c_65, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_62])).
% 1.82/1.17  tff(c_66, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_65])).
% 1.82/1.17  tff(c_16, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.17  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.17  tff(c_103, plain, (![B_38, A_39]: (~r2_hidden(B_38, A_39) | k4_xboole_0(A_39, k1_tarski(B_38))!=A_39)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.82/1.17  tff(c_135, plain, (![B_42]: (~r2_hidden(B_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_103])).
% 1.82/1.17  tff(c_139, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_135])).
% 1.82/1.17  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_139])).
% 1.82/1.17  tff(c_145, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_65])).
% 1.82/1.17  tff(c_144, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_65])).
% 1.82/1.17  tff(c_150, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.17  tff(c_160, plain, (![B_44]: (k3_xboole_0(k1_xboole_0, B_44)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_150, c_4])).
% 1.82/1.17  tff(c_218, plain, (![B_50, A_51]: (k9_relat_1(B_50, k3_xboole_0(k1_relat_1(B_50), A_51))=k9_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.82/1.17  tff(c_227, plain, (![A_51]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_51))=k9_relat_1(k1_xboole_0, A_51) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_218])).
% 1.82/1.17  tff(c_231, plain, (![A_51]: (k9_relat_1(k1_xboole_0, A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_145, c_144, c_160, c_227])).
% 1.82/1.17  tff(c_26, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.82/1.17  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_231, c_26])).
% 1.82/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.17  
% 1.82/1.17  Inference rules
% 1.82/1.17  ----------------------
% 1.82/1.17  #Ref     : 0
% 1.82/1.17  #Sup     : 50
% 1.82/1.17  #Fact    : 0
% 1.82/1.17  #Define  : 0
% 1.82/1.17  #Split   : 1
% 1.82/1.17  #Chain   : 0
% 1.82/1.17  #Close   : 0
% 1.82/1.17  
% 1.82/1.17  Ordering : KBO
% 1.82/1.17  
% 1.82/1.17  Simplification rules
% 1.82/1.17  ----------------------
% 1.82/1.17  #Subsume      : 0
% 1.82/1.17  #Demod        : 13
% 1.82/1.17  #Tautology    : 38
% 1.82/1.17  #SimpNegUnit  : 1
% 1.82/1.17  #BackRed      : 1
% 1.82/1.17  
% 1.82/1.17  #Partial instantiations: 0
% 1.82/1.17  #Strategies tried      : 1
% 1.82/1.17  
% 1.82/1.17  Timing (in seconds)
% 1.82/1.17  ----------------------
% 1.82/1.17  Preprocessing        : 0.27
% 1.82/1.17  Parsing              : 0.14
% 1.82/1.17  CNF conversion       : 0.02
% 1.82/1.17  Main loop            : 0.14
% 1.82/1.17  Inferencing          : 0.06
% 1.82/1.17  Reduction            : 0.04
% 1.82/1.17  Demodulation         : 0.03
% 1.82/1.17  BG Simplification    : 0.01
% 1.82/1.17  Subsumption          : 0.01
% 1.82/1.17  Abstraction          : 0.01
% 1.82/1.17  MUC search           : 0.00
% 1.82/1.17  Cooper               : 0.00
% 1.82/1.17  Total                : 0.43
% 1.82/1.17  Index Insertion      : 0.00
% 1.82/1.17  Index Deletion       : 0.00
% 1.82/1.17  Index Matching       : 0.00
% 1.82/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
