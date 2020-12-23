%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:29 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   49 (  49 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_1'(A_36),A_36)
      | v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [A_66,B_67] :
      ( ~ r2_hidden(A_66,B_67)
      | ~ r1_xboole_0(k1_tarski(A_66),B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    ! [A_68] : ~ r2_hidden(A_68,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_84,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_79])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_86,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(k10_relat_1(B_71,A_72),k1_relat_1(B_71))
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_92,plain,(
    ! [A_72] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_72),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_86])).

tff(c_96,plain,(
    ! [A_73] : r1_tarski(k10_relat_1(k1_xboole_0,A_73),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_92])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [A_73] : k3_xboole_0(k10_relat_1(k1_xboole_0,A_73),k1_xboole_0) = k10_relat_1(k1_xboole_0,A_73) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_101,plain,(
    ! [A_73] : k10_relat_1(k1_xboole_0,A_73) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_99])).

tff(c_36,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:28:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.13  
% 1.83/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.13  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.83/1.13  
% 1.83/1.13  %Foreground sorts:
% 1.83/1.13  
% 1.83/1.13  
% 1.83/1.13  %Background operators:
% 1.83/1.13  
% 1.83/1.13  
% 1.83/1.13  %Foreground operators:
% 1.83/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.83/1.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.83/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.83/1.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.83/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.83/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.83/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.83/1.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.83/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.83/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.83/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.83/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.83/1.13  
% 1.83/1.14  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.83/1.14  tff(f_62, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.83/1.14  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.83/1.14  tff(f_50, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.83/1.14  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.83/1.14  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.83/1.14  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.83/1.14  tff(f_72, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.83/1.14  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.14  tff(c_28, plain, (![A_36]: (r2_hidden('#skF_1'(A_36), A_36) | v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.83/1.14  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.14  tff(c_73, plain, (![A_66, B_67]: (~r2_hidden(A_66, B_67) | ~r1_xboole_0(k1_tarski(A_66), B_67))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.83/1.14  tff(c_79, plain, (![A_68]: (~r2_hidden(A_68, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_73])).
% 1.83/1.14  tff(c_84, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_79])).
% 1.83/1.14  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.83/1.14  tff(c_86, plain, (![B_71, A_72]: (r1_tarski(k10_relat_1(B_71, A_72), k1_relat_1(B_71)) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.83/1.14  tff(c_92, plain, (![A_72]: (r1_tarski(k10_relat_1(k1_xboole_0, A_72), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_86])).
% 1.83/1.14  tff(c_96, plain, (![A_73]: (r1_tarski(k10_relat_1(k1_xboole_0, A_73), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_92])).
% 1.83/1.14  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.14  tff(c_99, plain, (![A_73]: (k3_xboole_0(k10_relat_1(k1_xboole_0, A_73), k1_xboole_0)=k10_relat_1(k1_xboole_0, A_73))), inference(resolution, [status(thm)], [c_96, c_2])).
% 1.83/1.14  tff(c_101, plain, (![A_73]: (k10_relat_1(k1_xboole_0, A_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_99])).
% 1.83/1.14  tff(c_36, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.83/1.14  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_36])).
% 1.83/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.14  
% 1.83/1.14  Inference rules
% 1.83/1.14  ----------------------
% 1.83/1.14  #Ref     : 0
% 1.83/1.14  #Sup     : 17
% 1.83/1.14  #Fact    : 0
% 1.83/1.14  #Define  : 0
% 1.83/1.14  #Split   : 0
% 1.83/1.14  #Chain   : 0
% 1.83/1.14  #Close   : 0
% 1.83/1.14  
% 1.83/1.14  Ordering : KBO
% 1.83/1.14  
% 1.83/1.14  Simplification rules
% 1.83/1.14  ----------------------
% 1.83/1.14  #Subsume      : 0
% 1.83/1.14  #Demod        : 4
% 1.83/1.14  #Tautology    : 12
% 1.83/1.14  #SimpNegUnit  : 0
% 1.83/1.14  #BackRed      : 2
% 1.83/1.14  
% 1.83/1.14  #Partial instantiations: 0
% 1.83/1.14  #Strategies tried      : 1
% 1.83/1.14  
% 1.83/1.14  Timing (in seconds)
% 1.83/1.14  ----------------------
% 1.83/1.14  Preprocessing        : 0.29
% 1.83/1.14  Parsing              : 0.15
% 1.83/1.14  CNF conversion       : 0.02
% 1.83/1.14  Main loop            : 0.10
% 1.83/1.14  Inferencing          : 0.04
% 1.83/1.14  Reduction            : 0.03
% 1.83/1.14  Demodulation         : 0.03
% 1.83/1.15  BG Simplification    : 0.01
% 1.83/1.15  Subsumption          : 0.01
% 1.83/1.15  Abstraction          : 0.01
% 1.83/1.15  MUC search           : 0.00
% 1.83/1.15  Cooper               : 0.00
% 1.83/1.15  Total                : 0.42
% 1.83/1.15  Index Insertion      : 0.00
% 1.83/1.15  Index Deletion       : 0.00
% 1.83/1.15  Index Matching       : 0.00
% 1.83/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
