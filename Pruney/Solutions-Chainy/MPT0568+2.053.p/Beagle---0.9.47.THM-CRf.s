%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:27 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   46 (  75 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  88 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_60,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_59,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_40,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_47,plain,(
    ! [A_68] : v1_relat_1(k6_relat_1(A_68)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_49,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_47])).

tff(c_242,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden('#skF_2'(A_129,B_130,C_131),B_130)
      | r2_hidden('#skF_3'(A_129,B_130,C_131),C_131)
      | k10_relat_1(A_129,B_130) = C_131
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_75,plain,(
    ! [B_73,A_74] :
      ( ~ r2_hidden(B_73,A_74)
      | k4_xboole_0(A_74,k1_tarski(B_73)) != A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,(
    ! [B_73] : ~ r2_hidden(B_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_326,plain,(
    ! [A_132,C_133] :
      ( r2_hidden('#skF_3'(A_132,k1_xboole_0,C_133),C_133)
      | k10_relat_1(A_132,k1_xboole_0) = C_133
      | ~ v1_relat_1(A_132) ) ),
    inference(resolution,[status(thm)],[c_242,c_80])).

tff(c_370,plain,(
    ! [A_134] :
      ( k10_relat_1(A_134,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_134) ) ),
    inference(resolution,[status(thm)],[c_326,c_80])).

tff(c_377,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_370])).

tff(c_172,plain,(
    ! [D_115,A_116,B_117] :
      ( r2_hidden(k4_tarski(D_115,'#skF_4'(A_116,B_117,k10_relat_1(A_116,B_117),D_115)),A_116)
      | ~ r2_hidden(D_115,k10_relat_1(A_116,B_117))
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_190,plain,(
    ! [D_115,B_117] :
      ( ~ r2_hidden(D_115,k10_relat_1(k1_xboole_0,B_117))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_172,c_80])).

tff(c_197,plain,(
    ! [D_115,B_117] : ~ r2_hidden(D_115,k10_relat_1(k1_xboole_0,B_117)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_190])).

tff(c_470,plain,(
    ! [B_140,A_141] :
      ( k10_relat_1(k1_xboole_0,B_140) = k10_relat_1(A_141,k1_xboole_0)
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_326,c_197])).

tff(c_472,plain,(
    ! [B_140] : k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,B_140) ),
    inference(resolution,[status(thm)],[c_49,c_470])).

tff(c_476,plain,(
    ! [B_140] : k10_relat_1(k1_xboole_0,B_140) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_472])).

tff(c_42,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:15:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.33  
% 2.45/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.33  %$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.45/1.33  
% 2.45/1.33  %Foreground sorts:
% 2.45/1.33  
% 2.45/1.33  
% 2.45/1.33  %Background operators:
% 2.45/1.33  
% 2.45/1.33  
% 2.45/1.33  %Foreground operators:
% 2.45/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.45/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.45/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.45/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.45/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.45/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.45/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.45/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.45/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.45/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.45/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.45/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.45/1.33  
% 2.45/1.34  tff(f_60, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.45/1.34  tff(f_59, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.45/1.34  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 2.45/1.34  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.45/1.34  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.45/1.34  tff(f_63, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.45/1.34  tff(c_40, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.45/1.34  tff(c_47, plain, (![A_68]: (v1_relat_1(k6_relat_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.34  tff(c_49, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_47])).
% 2.45/1.34  tff(c_242, plain, (![A_129, B_130, C_131]: (r2_hidden('#skF_2'(A_129, B_130, C_131), B_130) | r2_hidden('#skF_3'(A_129, B_130, C_131), C_131) | k10_relat_1(A_129, B_130)=C_131 | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.45/1.34  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.34  tff(c_75, plain, (![B_73, A_74]: (~r2_hidden(B_73, A_74) | k4_xboole_0(A_74, k1_tarski(B_73))!=A_74)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.45/1.34  tff(c_80, plain, (![B_73]: (~r2_hidden(B_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 2.45/1.34  tff(c_326, plain, (![A_132, C_133]: (r2_hidden('#skF_3'(A_132, k1_xboole_0, C_133), C_133) | k10_relat_1(A_132, k1_xboole_0)=C_133 | ~v1_relat_1(A_132))), inference(resolution, [status(thm)], [c_242, c_80])).
% 2.45/1.34  tff(c_370, plain, (![A_134]: (k10_relat_1(A_134, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_134))), inference(resolution, [status(thm)], [c_326, c_80])).
% 2.45/1.34  tff(c_377, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_49, c_370])).
% 2.45/1.34  tff(c_172, plain, (![D_115, A_116, B_117]: (r2_hidden(k4_tarski(D_115, '#skF_4'(A_116, B_117, k10_relat_1(A_116, B_117), D_115)), A_116) | ~r2_hidden(D_115, k10_relat_1(A_116, B_117)) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.45/1.34  tff(c_190, plain, (![D_115, B_117]: (~r2_hidden(D_115, k10_relat_1(k1_xboole_0, B_117)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_172, c_80])).
% 2.45/1.34  tff(c_197, plain, (![D_115, B_117]: (~r2_hidden(D_115, k10_relat_1(k1_xboole_0, B_117)))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_190])).
% 2.45/1.34  tff(c_470, plain, (![B_140, A_141]: (k10_relat_1(k1_xboole_0, B_140)=k10_relat_1(A_141, k1_xboole_0) | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_326, c_197])).
% 2.45/1.34  tff(c_472, plain, (![B_140]: (k10_relat_1(k1_xboole_0, k1_xboole_0)=k10_relat_1(k1_xboole_0, B_140))), inference(resolution, [status(thm)], [c_49, c_470])).
% 2.45/1.34  tff(c_476, plain, (![B_140]: (k10_relat_1(k1_xboole_0, B_140)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_377, c_472])).
% 2.45/1.34  tff(c_42, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.45/1.34  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_476, c_42])).
% 2.45/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.34  
% 2.45/1.34  Inference rules
% 2.45/1.34  ----------------------
% 2.45/1.34  #Ref     : 0
% 2.45/1.34  #Sup     : 92
% 2.45/1.34  #Fact    : 0
% 2.45/1.34  #Define  : 0
% 2.45/1.34  #Split   : 0
% 2.45/1.34  #Chain   : 0
% 2.45/1.34  #Close   : 0
% 2.45/1.34  
% 2.45/1.34  Ordering : KBO
% 2.45/1.34  
% 2.45/1.34  Simplification rules
% 2.45/1.34  ----------------------
% 2.45/1.34  #Subsume      : 19
% 2.45/1.34  #Demod        : 35
% 2.45/1.34  #Tautology    : 27
% 2.45/1.34  #SimpNegUnit  : 5
% 2.45/1.34  #BackRed      : 5
% 2.45/1.34  
% 2.45/1.34  #Partial instantiations: 0
% 2.45/1.34  #Strategies tried      : 1
% 2.45/1.34  
% 2.45/1.34  Timing (in seconds)
% 2.45/1.34  ----------------------
% 2.45/1.34  Preprocessing        : 0.31
% 2.45/1.34  Parsing              : 0.16
% 2.45/1.34  CNF conversion       : 0.02
% 2.45/1.34  Main loop            : 0.23
% 2.45/1.34  Inferencing          : 0.09
% 2.45/1.34  Reduction            : 0.06
% 2.45/1.34  Demodulation         : 0.04
% 2.45/1.34  BG Simplification    : 0.02
% 2.45/1.34  Subsumption          : 0.05
% 2.45/1.34  Abstraction          : 0.02
% 2.45/1.34  MUC search           : 0.00
% 2.45/1.34  Cooper               : 0.00
% 2.45/1.34  Total                : 0.56
% 2.45/1.34  Index Insertion      : 0.00
% 2.45/1.34  Index Deletion       : 0.00
% 2.45/1.34  Index Matching       : 0.00
% 2.45/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
