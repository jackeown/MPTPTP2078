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
% DateTime   : Thu Dec  3 10:01:47 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   43 (  47 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  73 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_119,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(k2_relat_1(B_32),A_33)
      | k10_relat_1(B_32,A_33) != k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_159,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,k2_relat_1(B_41))
      | k10_relat_1(B_41,A_40) != k1_xboole_0
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ r1_xboole_0(B_6,A_5)
      | ~ r1_tarski(B_6,A_5)
      | v1_xboole_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_172,plain,(
    ! [A_42,B_43] :
      ( ~ r1_tarski(A_42,k2_relat_1(B_43))
      | v1_xboole_0(A_42)
      | k10_relat_1(B_43,A_42) != k1_xboole_0
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_159,c_8])).

tff(c_175,plain,
    ( v1_xboole_0('#skF_1')
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_172])).

tff(c_182,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_175])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_37,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ! [A_4] : r1_xboole_0(k1_xboole_0,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_37])).

tff(c_64,plain,(
    ! [B_25,A_26] :
      ( ~ r1_xboole_0(B_25,A_26)
      | ~ r1_tarski(B_25,A_26)
      | v1_xboole_0(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_4] :
      ( ~ r1_tarski(k1_xboole_0,A_4)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_81,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_73])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ v1_xboole_0(B_10)
      | B_10 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_188,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_182,c_85])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:56:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.20  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.88/1.20  
% 1.88/1.20  %Foreground sorts:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Background operators:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Foreground operators:
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.88/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.20  
% 1.88/1.21  tff(f_68, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 1.88/1.21  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 1.88/1.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.88/1.21  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.88/1.21  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.88/1.21  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.88/1.21  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.88/1.21  tff(f_51, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.88/1.21  tff(c_22, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.21  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.21  tff(c_18, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.21  tff(c_20, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.21  tff(c_119, plain, (![B_32, A_33]: (r1_xboole_0(k2_relat_1(B_32), A_33) | k10_relat_1(B_32, A_33)!=k1_xboole_0 | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.21  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.21  tff(c_159, plain, (![A_40, B_41]: (r1_xboole_0(A_40, k2_relat_1(B_41)) | k10_relat_1(B_41, A_40)!=k1_xboole_0 | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_119, c_2])).
% 1.88/1.21  tff(c_8, plain, (![B_6, A_5]: (~r1_xboole_0(B_6, A_5) | ~r1_tarski(B_6, A_5) | v1_xboole_0(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.21  tff(c_172, plain, (![A_42, B_43]: (~r1_tarski(A_42, k2_relat_1(B_43)) | v1_xboole_0(A_42) | k10_relat_1(B_43, A_42)!=k1_xboole_0 | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_159, c_8])).
% 1.88/1.21  tff(c_175, plain, (v1_xboole_0('#skF_1') | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_172])).
% 1.88/1.21  tff(c_182, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_175])).
% 1.88/1.21  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.21  tff(c_6, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.21  tff(c_37, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.88/1.21  tff(c_40, plain, (![A_4]: (r1_xboole_0(k1_xboole_0, A_4))), inference(superposition, [status(thm), theory('equality')], [c_6, c_37])).
% 1.88/1.21  tff(c_64, plain, (![B_25, A_26]: (~r1_xboole_0(B_25, A_26) | ~r1_tarski(B_25, A_26) | v1_xboole_0(B_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.21  tff(c_73, plain, (![A_4]: (~r1_tarski(k1_xboole_0, A_4) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_64])).
% 1.88/1.21  tff(c_81, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_73])).
% 1.88/1.21  tff(c_12, plain, (![B_10, A_9]: (~v1_xboole_0(B_10) | B_10=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.21  tff(c_85, plain, (![A_9]: (k1_xboole_0=A_9 | ~v1_xboole_0(A_9))), inference(resolution, [status(thm)], [c_81, c_12])).
% 1.88/1.21  tff(c_188, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_182, c_85])).
% 1.88/1.21  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_188])).
% 1.88/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  Inference rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Ref     : 0
% 1.88/1.21  #Sup     : 38
% 1.88/1.21  #Fact    : 0
% 1.88/1.21  #Define  : 0
% 1.88/1.21  #Split   : 0
% 1.88/1.21  #Chain   : 0
% 1.88/1.21  #Close   : 0
% 1.88/1.21  
% 1.88/1.21  Ordering : KBO
% 1.88/1.21  
% 1.88/1.21  Simplification rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Subsume      : 3
% 1.88/1.21  #Demod        : 12
% 1.88/1.21  #Tautology    : 17
% 1.88/1.21  #SimpNegUnit  : 1
% 1.88/1.21  #BackRed      : 0
% 1.88/1.21  
% 1.88/1.21  #Partial instantiations: 0
% 1.88/1.21  #Strategies tried      : 1
% 1.88/1.21  
% 1.88/1.21  Timing (in seconds)
% 1.88/1.21  ----------------------
% 1.97/1.21  Preprocessing        : 0.28
% 1.97/1.21  Parsing              : 0.16
% 1.97/1.21  CNF conversion       : 0.02
% 1.97/1.21  Main loop            : 0.16
% 1.97/1.21  Inferencing          : 0.07
% 1.97/1.21  Reduction            : 0.05
% 1.97/1.21  Demodulation         : 0.03
% 1.97/1.21  BG Simplification    : 0.01
% 1.97/1.21  Subsumption          : 0.03
% 1.97/1.21  Abstraction          : 0.01
% 1.97/1.21  MUC search           : 0.00
% 1.97/1.21  Cooper               : 0.00
% 1.97/1.21  Total                : 0.47
% 1.97/1.21  Index Insertion      : 0.00
% 1.97/1.21  Index Deletion       : 0.00
% 1.97/1.21  Index Matching       : 0.00
% 1.97/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
