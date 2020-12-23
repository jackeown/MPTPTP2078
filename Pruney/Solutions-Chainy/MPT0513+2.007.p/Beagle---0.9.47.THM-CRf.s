%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:59 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   48 (  48 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  44 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_81,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_47] :
      ( v1_relat_1(A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_34,plain,(
    ! [B_45,A_44] :
      ( r1_tarski(k7_relat_1(B_45,A_44),B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_65,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_162,plain,(
    ! [B_78,A_79] :
      ( k3_xboole_0(k7_relat_1(B_78,A_79),B_78) = k7_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,k3_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_85,plain,(
    ! [A_63,B_64] :
      ( ~ r1_xboole_0(A_63,B_64)
      | v1_xboole_0(k3_xboole_0(A_63,B_64)) ) ),
    inference(resolution,[status(thm)],[c_4,c_79])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_94,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_xboole_0(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_98,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_94])).

tff(c_178,plain,(
    ! [A_79] :
      ( k7_relat_1(k1_xboole_0,A_79) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_98])).

tff(c_194,plain,(
    ! [A_79] : k7_relat_1(k1_xboole_0,A_79) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_178])).

tff(c_36,plain,(
    k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:08:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.56  
% 2.35/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.35/1.57  
% 2.35/1.57  %Foreground sorts:
% 2.35/1.57  
% 2.35/1.57  
% 2.35/1.57  %Background operators:
% 2.35/1.57  
% 2.35/1.57  
% 2.35/1.57  %Foreground operators:
% 2.35/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.35/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.35/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.35/1.57  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.35/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.35/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.35/1.57  
% 2.35/1.58  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.35/1.58  tff(f_74, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.35/1.58  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.35/1.58  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.35/1.58  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.35/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.35/1.58  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.35/1.58  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.35/1.58  tff(f_81, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 2.35/1.58  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.35/1.58  tff(c_38, plain, (![A_47]: (v1_relat_1(A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.35/1.58  tff(c_42, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_38])).
% 2.35/1.58  tff(c_34, plain, (![B_45, A_44]: (r1_tarski(k7_relat_1(B_45, A_44), B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.35/1.58  tff(c_65, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.35/1.58  tff(c_162, plain, (![B_78, A_79]: (k3_xboole_0(k7_relat_1(B_78, A_79), B_78)=k7_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_34, c_65])).
% 2.35/1.58  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.58  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.58  tff(c_79, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.35/1.58  tff(c_85, plain, (![A_63, B_64]: (~r1_xboole_0(A_63, B_64) | v1_xboole_0(k3_xboole_0(A_63, B_64)))), inference(resolution, [status(thm)], [c_4, c_79])).
% 2.35/1.58  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.35/1.58  tff(c_94, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_xboole_0(A_65, B_66))), inference(resolution, [status(thm)], [c_85, c_8])).
% 2.35/1.58  tff(c_98, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_94])).
% 2.35/1.58  tff(c_178, plain, (![A_79]: (k7_relat_1(k1_xboole_0, A_79)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_162, c_98])).
% 2.35/1.58  tff(c_194, plain, (![A_79]: (k7_relat_1(k1_xboole_0, A_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_178])).
% 2.35/1.58  tff(c_36, plain, (k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.35/1.58  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_36])).
% 2.35/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.58  
% 2.35/1.58  Inference rules
% 2.35/1.58  ----------------------
% 2.35/1.58  #Ref     : 0
% 2.35/1.58  #Sup     : 34
% 2.35/1.58  #Fact    : 0
% 2.35/1.58  #Define  : 0
% 2.35/1.58  #Split   : 0
% 2.35/1.58  #Chain   : 0
% 2.35/1.58  #Close   : 0
% 2.35/1.58  
% 2.35/1.58  Ordering : KBO
% 2.35/1.58  
% 2.35/1.58  Simplification rules
% 2.35/1.58  ----------------------
% 2.35/1.58  #Subsume      : 0
% 2.35/1.58  #Demod        : 12
% 2.35/1.58  #Tautology    : 19
% 2.35/1.58  #SimpNegUnit  : 1
% 2.35/1.58  #BackRed      : 1
% 2.35/1.58  
% 2.35/1.58  #Partial instantiations: 0
% 2.35/1.58  #Strategies tried      : 1
% 2.35/1.58  
% 2.35/1.58  Timing (in seconds)
% 2.35/1.58  ----------------------
% 2.35/1.59  Preprocessing        : 0.49
% 2.35/1.59  Parsing              : 0.27
% 2.35/1.59  CNF conversion       : 0.03
% 2.35/1.59  Main loop            : 0.18
% 2.35/1.59  Inferencing          : 0.08
% 2.35/1.59  Reduction            : 0.06
% 2.35/1.59  Demodulation         : 0.04
% 2.35/1.59  BG Simplification    : 0.02
% 2.35/1.59  Subsumption          : 0.02
% 2.35/1.59  Abstraction          : 0.01
% 2.35/1.59  MUC search           : 0.00
% 2.35/1.59  Cooper               : 0.00
% 2.35/1.59  Total                : 0.71
% 2.35/1.59  Index Insertion      : 0.00
% 2.35/1.59  Index Deletion       : 0.00
% 2.35/1.59  Index Matching       : 0.00
% 2.35/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
