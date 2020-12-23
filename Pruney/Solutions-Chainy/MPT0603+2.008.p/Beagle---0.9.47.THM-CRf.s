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
% DateTime   : Thu Dec  3 10:02:24 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   47 (  51 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  56 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_81,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_2'(A_57,B_58),B_58)
      | r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [B_58,A_57] :
      ( ~ v1_xboole_0(B_58)
      | r1_xboole_0(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_194,plain,(
    ! [B_80,A_81] :
      ( k7_relat_1(B_80,A_81) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_80),A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_222,plain,(
    ! [B_84,B_85] :
      ( k7_relat_1(B_84,B_85) = k1_xboole_0
      | ~ v1_relat_1(B_84)
      | ~ v1_xboole_0(B_85) ) ),
    inference(resolution,[status(thm)],[c_85,c_194])).

tff(c_226,plain,(
    ! [B_86] :
      ( k7_relat_1('#skF_5',B_86) = k1_xboole_0
      | ~ v1_xboole_0(B_86) ) ),
    inference(resolution,[status(thm)],[c_42,c_222])).

tff(c_230,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_226])).

tff(c_40,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_277,plain,(
    ! [C_101,A_102,B_103] :
      ( k7_relat_1(k7_relat_1(C_101,A_102),B_103) = k7_relat_1(C_101,k3_xboole_0(A_102,B_103))
      | ~ v1_relat_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    k7_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_286,plain,
    ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_38])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_230,c_76,c_286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.27  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.13/1.27  
% 2.13/1.27  %Foreground sorts:
% 2.13/1.27  
% 2.13/1.27  
% 2.13/1.27  %Background operators:
% 2.13/1.27  
% 2.13/1.27  
% 2.13/1.27  %Foreground operators:
% 2.13/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.13/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.13/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.13/1.27  
% 2.13/1.27  tff(f_85, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.13/1.27  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.13/1.27  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.13/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.13/1.27  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.13/1.27  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.13/1.27  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.13/1.27  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.13/1.27  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.13/1.27  tff(c_81, plain, (![A_57, B_58]: (r2_hidden('#skF_2'(A_57, B_58), B_58) | r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.27  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.27  tff(c_85, plain, (![B_58, A_57]: (~v1_xboole_0(B_58) | r1_xboole_0(A_57, B_58))), inference(resolution, [status(thm)], [c_81, c_2])).
% 2.13/1.27  tff(c_194, plain, (![B_80, A_81]: (k7_relat_1(B_80, A_81)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_80), A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.27  tff(c_222, plain, (![B_84, B_85]: (k7_relat_1(B_84, B_85)=k1_xboole_0 | ~v1_relat_1(B_84) | ~v1_xboole_0(B_85))), inference(resolution, [status(thm)], [c_85, c_194])).
% 2.13/1.27  tff(c_226, plain, (![B_86]: (k7_relat_1('#skF_5', B_86)=k1_xboole_0 | ~v1_xboole_0(B_86))), inference(resolution, [status(thm)], [c_42, c_222])).
% 2.13/1.27  tff(c_230, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_226])).
% 2.13/1.27  tff(c_40, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.13/1.27  tff(c_68, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.27  tff(c_76, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_68])).
% 2.13/1.27  tff(c_277, plain, (![C_101, A_102, B_103]: (k7_relat_1(k7_relat_1(C_101, A_102), B_103)=k7_relat_1(C_101, k3_xboole_0(A_102, B_103)) | ~v1_relat_1(C_101))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.13/1.27  tff(c_38, plain, (k7_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.13/1.27  tff(c_286, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_277, c_38])).
% 2.13/1.27  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_230, c_76, c_286])).
% 2.13/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  Inference rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Ref     : 0
% 2.13/1.27  #Sup     : 61
% 2.13/1.27  #Fact    : 0
% 2.13/1.27  #Define  : 0
% 2.13/1.27  #Split   : 1
% 2.13/1.28  #Chain   : 0
% 2.13/1.28  #Close   : 0
% 2.13/1.28  
% 2.13/1.28  Ordering : KBO
% 2.13/1.28  
% 2.13/1.28  Simplification rules
% 2.13/1.28  ----------------------
% 2.13/1.28  #Subsume      : 3
% 2.13/1.28  #Demod        : 6
% 2.13/1.28  #Tautology    : 27
% 2.13/1.28  #SimpNegUnit  : 0
% 2.13/1.28  #BackRed      : 0
% 2.13/1.28  
% 2.13/1.28  #Partial instantiations: 0
% 2.13/1.28  #Strategies tried      : 1
% 2.13/1.28  
% 2.13/1.28  Timing (in seconds)
% 2.13/1.28  ----------------------
% 2.13/1.28  Preprocessing        : 0.31
% 2.13/1.28  Parsing              : 0.17
% 2.13/1.28  CNF conversion       : 0.02
% 2.13/1.28  Main loop            : 0.20
% 2.13/1.28  Inferencing          : 0.08
% 2.13/1.28  Reduction            : 0.05
% 2.13/1.28  Demodulation         : 0.04
% 2.13/1.28  BG Simplification    : 0.01
% 2.13/1.28  Subsumption          : 0.04
% 2.13/1.28  Abstraction          : 0.01
% 2.13/1.28  MUC search           : 0.00
% 2.13/1.28  Cooper               : 0.00
% 2.13/1.28  Total                : 0.54
% 2.13/1.28  Index Insertion      : 0.00
% 2.13/1.28  Index Deletion       : 0.00
% 2.13/1.28  Index Matching       : 0.00
% 2.13/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
