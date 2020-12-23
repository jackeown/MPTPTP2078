%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:28 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   49 (  65 expanded)
%              Number of leaves         :   31 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  69 expanded)
%              Number of equality atoms :   18 (  37 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_99,plain,(
    ! [A_46] :
      ( k8_relat_1(k2_relat_1(A_46),A_46) = A_46
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_108,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_99])).

tff(c_111,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_24,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),A_15)
      | v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [B_54,A_55] :
      ( ~ r2_hidden(B_54,A_55)
      | k4_xboole_0(A_55,k1_tarski(B_54)) != A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_154,plain,(
    ! [B_56] : ~ r2_hidden(B_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_144])).

tff(c_158,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_154])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_158])).

tff(c_164,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_163,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_240,plain,(
    ! [B_71,A_72,C_73] :
      ( k8_relat_1(B_71,k8_relat_1(A_72,C_73)) = k8_relat_1(A_72,C_73)
      | ~ r1_tarski(A_72,B_71)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_259,plain,(
    ! [B_71] :
      ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(B_71,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_71)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_240])).

tff(c_271,plain,(
    ! [B_71] : k8_relat_1(B_71,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_4,c_163,c_259])).

tff(c_34,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.29  
% 1.97/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.30  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.97/1.30  
% 1.97/1.30  %Foreground sorts:
% 1.97/1.30  
% 1.97/1.30  
% 1.97/1.30  %Background operators:
% 1.97/1.30  
% 1.97/1.30  
% 1.97/1.30  %Foreground operators:
% 1.97/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.97/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.97/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.97/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.97/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.97/1.30  
% 1.97/1.31  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.97/1.31  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 1.97/1.31  tff(f_54, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.97/1.31  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.97/1.31  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.97/1.31  tff(f_29, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.97/1.31  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 1.97/1.31  tff(f_70, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.97/1.31  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.97/1.31  tff(c_99, plain, (![A_46]: (k8_relat_1(k2_relat_1(A_46), A_46)=A_46 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.97/1.31  tff(c_108, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_99])).
% 1.97/1.31  tff(c_111, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_108])).
% 1.97/1.31  tff(c_24, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.97/1.31  tff(c_6, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.31  tff(c_144, plain, (![B_54, A_55]: (~r2_hidden(B_54, A_55) | k4_xboole_0(A_55, k1_tarski(B_54))!=A_55)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.31  tff(c_154, plain, (![B_56]: (~r2_hidden(B_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_144])).
% 1.97/1.31  tff(c_158, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_154])).
% 1.97/1.31  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_158])).
% 1.97/1.31  tff(c_164, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_108])).
% 1.97/1.31  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.31  tff(c_163, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_108])).
% 1.97/1.31  tff(c_240, plain, (![B_71, A_72, C_73]: (k8_relat_1(B_71, k8_relat_1(A_72, C_73))=k8_relat_1(A_72, C_73) | ~r1_tarski(A_72, B_71) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.31  tff(c_259, plain, (![B_71]: (k8_relat_1(k1_xboole_0, k1_xboole_0)=k8_relat_1(B_71, k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_71) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_163, c_240])).
% 1.97/1.31  tff(c_271, plain, (![B_71]: (k8_relat_1(B_71, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_4, c_163, c_259])).
% 1.97/1.31  tff(c_34, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.97/1.31  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_271, c_34])).
% 1.97/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.31  
% 1.97/1.31  Inference rules
% 1.97/1.31  ----------------------
% 1.97/1.31  #Ref     : 0
% 1.97/1.31  #Sup     : 55
% 1.97/1.31  #Fact    : 0
% 1.97/1.31  #Define  : 0
% 1.97/1.31  #Split   : 1
% 1.97/1.31  #Chain   : 0
% 1.97/1.31  #Close   : 0
% 1.97/1.31  
% 1.97/1.31  Ordering : KBO
% 1.97/1.31  
% 1.97/1.31  Simplification rules
% 1.97/1.31  ----------------------
% 1.97/1.31  #Subsume      : 0
% 1.97/1.31  #Demod        : 7
% 1.97/1.31  #Tautology    : 45
% 1.97/1.31  #SimpNegUnit  : 1
% 1.97/1.31  #BackRed      : 1
% 1.97/1.31  
% 1.97/1.31  #Partial instantiations: 0
% 1.97/1.31  #Strategies tried      : 1
% 1.97/1.31  
% 1.97/1.31  Timing (in seconds)
% 1.97/1.31  ----------------------
% 1.97/1.31  Preprocessing        : 0.33
% 1.97/1.31  Parsing              : 0.17
% 1.97/1.31  CNF conversion       : 0.02
% 1.97/1.31  Main loop            : 0.16
% 1.97/1.31  Inferencing          : 0.07
% 1.97/1.31  Reduction            : 0.05
% 2.18/1.31  Demodulation         : 0.03
% 2.18/1.31  BG Simplification    : 0.01
% 2.18/1.31  Subsumption          : 0.02
% 2.18/1.31  Abstraction          : 0.01
% 2.18/1.31  MUC search           : 0.00
% 2.18/1.31  Cooper               : 0.00
% 2.18/1.31  Total                : 0.52
% 2.18/1.31  Index Insertion      : 0.00
% 2.18/1.31  Index Deletion       : 0.00
% 2.18/1.31  Index Matching       : 0.00
% 2.18/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
