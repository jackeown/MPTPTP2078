%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:37 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  84 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_75,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_30])).

tff(c_43,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(k1_tarski(A_20),B_21)
      | r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [B_21,A_20] :
      ( r1_xboole_0(B_21,k1_tarski(A_20))
      | r2_hidden(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_97,plain,(
    ! [B_35,A_36] :
      ( k10_relat_1(B_35,A_36) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_35),A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_209,plain,(
    ! [B_50,A_51] :
      ( k10_relat_1(B_50,k1_tarski(A_51)) = k1_xboole_0
      | ~ v1_relat_1(B_50)
      | r2_hidden(A_51,k2_relat_1(B_50)) ) ),
    inference(resolution,[status(thm)],[c_50,c_97])).

tff(c_212,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_209,c_75])).

tff(c_215,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_212])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_215])).

tff(c_218,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_219,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_293,plain,(
    ! [B_65,A_66] :
      ( r1_xboole_0(k2_relat_1(B_65),A_66)
      | k10_relat_1(B_65,A_66) != k1_xboole_0
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_369,plain,(
    ! [B_78,A_79] :
      ( k4_xboole_0(k2_relat_1(B_78),A_79) = k2_relat_1(B_78)
      | k10_relat_1(B_78,A_79) != k1_xboole_0
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_293,c_4])).

tff(c_14,plain,(
    ! [C_10,B_9] : ~ r2_hidden(C_10,k4_xboole_0(B_9,k1_tarski(C_10))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_418,plain,(
    ! [C_80,B_81] :
      ( ~ r2_hidden(C_80,k2_relat_1(B_81))
      | k10_relat_1(B_81,k1_tarski(C_80)) != k1_xboole_0
      | ~ v1_relat_1(B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_14])).

tff(c_424,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_219,c_418])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_218,c_424])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.35  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.21/1.35  
% 2.21/1.35  %Foreground sorts:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Background operators:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Foreground operators:
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.21/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.35  
% 2.21/1.36  tff(f_61, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.21/1.36  tff(f_40, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.21/1.36  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.21/1.36  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.21/1.36  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.21/1.36  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.21/1.36  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.21/1.36  tff(c_24, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.21/1.36  tff(c_75, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_24])).
% 2.21/1.36  tff(c_30, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.21/1.36  tff(c_92, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_75, c_30])).
% 2.21/1.36  tff(c_43, plain, (![A_20, B_21]: (r1_xboole_0(k1_tarski(A_20), B_21) | r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.21/1.36  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.36  tff(c_50, plain, (![B_21, A_20]: (r1_xboole_0(B_21, k1_tarski(A_20)) | r2_hidden(A_20, B_21))), inference(resolution, [status(thm)], [c_43, c_2])).
% 2.21/1.36  tff(c_97, plain, (![B_35, A_36]: (k10_relat_1(B_35, A_36)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_35), A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.36  tff(c_209, plain, (![B_50, A_51]: (k10_relat_1(B_50, k1_tarski(A_51))=k1_xboole_0 | ~v1_relat_1(B_50) | r2_hidden(A_51, k2_relat_1(B_50)))), inference(resolution, [status(thm)], [c_50, c_97])).
% 2.21/1.36  tff(c_212, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_209, c_75])).
% 2.21/1.36  tff(c_215, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_212])).
% 2.21/1.36  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_215])).
% 2.21/1.36  tff(c_218, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 2.21/1.36  tff(c_219, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_24])).
% 2.21/1.36  tff(c_293, plain, (![B_65, A_66]: (r1_xboole_0(k2_relat_1(B_65), A_66) | k10_relat_1(B_65, A_66)!=k1_xboole_0 | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.36  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.36  tff(c_369, plain, (![B_78, A_79]: (k4_xboole_0(k2_relat_1(B_78), A_79)=k2_relat_1(B_78) | k10_relat_1(B_78, A_79)!=k1_xboole_0 | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_293, c_4])).
% 2.21/1.36  tff(c_14, plain, (![C_10, B_9]: (~r2_hidden(C_10, k4_xboole_0(B_9, k1_tarski(C_10))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.36  tff(c_418, plain, (![C_80, B_81]: (~r2_hidden(C_80, k2_relat_1(B_81)) | k10_relat_1(B_81, k1_tarski(C_80))!=k1_xboole_0 | ~v1_relat_1(B_81))), inference(superposition, [status(thm), theory('equality')], [c_369, c_14])).
% 2.21/1.36  tff(c_424, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_219, c_418])).
% 2.21/1.36  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_218, c_424])).
% 2.21/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.36  
% 2.21/1.36  Inference rules
% 2.21/1.36  ----------------------
% 2.21/1.36  #Ref     : 0
% 2.21/1.36  #Sup     : 88
% 2.21/1.36  #Fact    : 0
% 2.21/1.36  #Define  : 0
% 2.21/1.36  #Split   : 1
% 2.21/1.36  #Chain   : 0
% 2.21/1.36  #Close   : 0
% 2.21/1.36  
% 2.21/1.36  Ordering : KBO
% 2.21/1.36  
% 2.21/1.36  Simplification rules
% 2.21/1.36  ----------------------
% 2.21/1.36  #Subsume      : 10
% 2.21/1.36  #Demod        : 5
% 2.21/1.36  #Tautology    : 54
% 2.21/1.36  #SimpNegUnit  : 2
% 2.21/1.36  #BackRed      : 0
% 2.21/1.36  
% 2.21/1.36  #Partial instantiations: 0
% 2.21/1.36  #Strategies tried      : 1
% 2.21/1.36  
% 2.21/1.36  Timing (in seconds)
% 2.21/1.36  ----------------------
% 2.21/1.36  Preprocessing        : 0.31
% 2.21/1.36  Parsing              : 0.16
% 2.21/1.36  CNF conversion       : 0.02
% 2.21/1.36  Main loop            : 0.23
% 2.21/1.37  Inferencing          : 0.09
% 2.21/1.37  Reduction            : 0.06
% 2.21/1.37  Demodulation         : 0.03
% 2.21/1.37  BG Simplification    : 0.02
% 2.21/1.37  Subsumption          : 0.04
% 2.21/1.37  Abstraction          : 0.01
% 2.21/1.37  MUC search           : 0.00
% 2.21/1.37  Cooper               : 0.00
% 2.21/1.37  Total                : 0.57
% 2.21/1.37  Index Insertion      : 0.00
% 2.21/1.37  Index Deletion       : 0.00
% 2.21/1.37  Index Matching       : 0.00
% 2.21/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
