%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:27 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   52 (  52 expanded)
%              Number of leaves         :   37 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_76,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_10,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_1'(A_40),A_40)
      | v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_120,plain,(
    ! [A_77,B_78] :
      ( k2_xboole_0(k1_tarski(A_77),B_78) = B_78
      | ~ r2_hidden(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [A_36,B_37] : k2_xboole_0(k1_tarski(A_36),B_37) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_144,plain,(
    ! [B_81,A_82] :
      ( k1_xboole_0 != B_81
      | ~ r2_hidden(A_82,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_28])).

tff(c_149,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_144])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_173,plain,(
    ! [A_88,B_89] :
      ( k8_relat_1(A_88,B_89) = B_89
      | ~ r1_tarski(k2_relat_1(B_89),A_88)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_180,plain,(
    ! [A_88] :
      ( k8_relat_1(A_88,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_88)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_173])).

tff(c_184,plain,(
    ! [A_90] :
      ( k8_relat_1(A_90,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_180])).

tff(c_188,plain,(
    ! [B_4] :
      ( k8_relat_1(B_4,k1_xboole_0) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_184])).

tff(c_191,plain,(
    ! [B_4] : k8_relat_1(B_4,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_188])).

tff(c_44,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:56:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.19  
% 2.02/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.19  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.02/1.19  
% 2.02/1.19  %Foreground sorts:
% 2.02/1.19  
% 2.02/1.19  
% 2.02/1.19  %Background operators:
% 2.02/1.19  
% 2.02/1.19  
% 2.02/1.19  %Foreground operators:
% 2.02/1.19  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.02/1.19  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.02/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.02/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.02/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.19  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.02/1.19  
% 2.02/1.20  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.02/1.20  tff(f_32, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.02/1.20  tff(f_67, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.02/1.20  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.02/1.20  tff(f_55, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.02/1.20  tff(f_76, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.02/1.20  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.02/1.20  tff(f_79, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 2.02/1.20  tff(c_10, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.20  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.20  tff(c_36, plain, (![A_40]: (r2_hidden('#skF_1'(A_40), A_40) | v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.20  tff(c_120, plain, (![A_77, B_78]: (k2_xboole_0(k1_tarski(A_77), B_78)=B_78 | ~r2_hidden(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.20  tff(c_28, plain, (![A_36, B_37]: (k2_xboole_0(k1_tarski(A_36), B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.02/1.20  tff(c_144, plain, (![B_81, A_82]: (k1_xboole_0!=B_81 | ~r2_hidden(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_120, c_28])).
% 2.02/1.20  tff(c_149, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_144])).
% 2.02/1.20  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.02/1.20  tff(c_173, plain, (![A_88, B_89]: (k8_relat_1(A_88, B_89)=B_89 | ~r1_tarski(k2_relat_1(B_89), A_88) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.02/1.20  tff(c_180, plain, (![A_88]: (k8_relat_1(A_88, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_88) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_173])).
% 2.02/1.20  tff(c_184, plain, (![A_90]: (k8_relat_1(A_90, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_90))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_180])).
% 2.02/1.20  tff(c_188, plain, (![B_4]: (k8_relat_1(B_4, k1_xboole_0)=k1_xboole_0 | k4_xboole_0(k1_xboole_0, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_184])).
% 2.02/1.20  tff(c_191, plain, (![B_4]: (k8_relat_1(B_4, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_188])).
% 2.02/1.20  tff(c_44, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.02/1.20  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_44])).
% 2.02/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.20  
% 2.02/1.20  Inference rules
% 2.02/1.20  ----------------------
% 2.02/1.20  #Ref     : 0
% 2.02/1.20  #Sup     : 35
% 2.02/1.20  #Fact    : 0
% 2.02/1.20  #Define  : 0
% 2.02/1.20  #Split   : 0
% 2.02/1.20  #Chain   : 0
% 2.02/1.20  #Close   : 0
% 2.02/1.20  
% 2.02/1.20  Ordering : KBO
% 2.02/1.20  
% 2.02/1.20  Simplification rules
% 2.02/1.20  ----------------------
% 2.02/1.20  #Subsume      : 0
% 2.02/1.20  #Demod        : 5
% 2.02/1.20  #Tautology    : 29
% 2.02/1.20  #SimpNegUnit  : 0
% 2.02/1.20  #BackRed      : 1
% 2.02/1.20  
% 2.02/1.20  #Partial instantiations: 0
% 2.02/1.20  #Strategies tried      : 1
% 2.02/1.20  
% 2.02/1.20  Timing (in seconds)
% 2.02/1.20  ----------------------
% 2.02/1.20  Preprocessing        : 0.32
% 2.02/1.20  Parsing              : 0.17
% 2.02/1.20  CNF conversion       : 0.02
% 2.02/1.20  Main loop            : 0.14
% 2.02/1.20  Inferencing          : 0.06
% 2.02/1.20  Reduction            : 0.04
% 2.02/1.20  Demodulation         : 0.03
% 2.02/1.20  BG Simplification    : 0.01
% 2.02/1.20  Subsumption          : 0.02
% 2.02/1.20  Abstraction          : 0.01
% 2.02/1.21  MUC search           : 0.00
% 2.02/1.21  Cooper               : 0.00
% 2.02/1.21  Total                : 0.49
% 2.02/1.21  Index Insertion      : 0.00
% 2.02/1.21  Index Deletion       : 0.00
% 2.02/1.21  Index Matching       : 0.00
% 2.02/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
