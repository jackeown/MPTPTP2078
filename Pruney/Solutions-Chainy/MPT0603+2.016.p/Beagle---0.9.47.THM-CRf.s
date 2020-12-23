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
% DateTime   : Thu Dec  3 10:02:25 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  61 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_47,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_98,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,B_59)
      | ~ r2_hidden(C_60,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [C_64] : ~ r2_hidden(C_64,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_98])).

tff(c_126,plain,(
    ! [B_4] : r1_xboole_0(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_10,c_117])).

tff(c_220,plain,(
    ! [A_71,B_72] :
      ( k7_relat_1(A_71,B_72) = k1_xboole_0
      | ~ r1_xboole_0(B_72,k1_relat_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_231,plain,(
    ! [A_73] :
      ( k7_relat_1(A_73,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_126,c_220])).

tff(c_235,plain,(
    k7_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_231])).

tff(c_36,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_61,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_61])).

tff(c_269,plain,(
    ! [C_84,A_85,B_86] :
      ( k7_relat_1(k7_relat_1(C_84,A_85),B_86) = k7_relat_1(C_84,k3_xboole_0(A_85,B_86))
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    k7_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_278,plain,
    ( k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_34])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_235,c_73,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.31  
% 1.97/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.31  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.97/1.31  
% 1.97/1.31  %Foreground sorts:
% 1.97/1.31  
% 1.97/1.31  
% 1.97/1.31  %Background operators:
% 1.97/1.31  
% 1.97/1.31  
% 1.97/1.31  %Foreground operators:
% 1.97/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.97/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.31  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.97/1.31  
% 2.24/1.32  tff(f_91, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.24/1.32  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.24/1.32  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.24/1.32  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.24/1.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.24/1.32  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.24/1.32  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.32  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.24/1.32  tff(c_12, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.32  tff(c_98, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, B_59) | ~r2_hidden(C_60, A_58))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.24/1.32  tff(c_117, plain, (![C_64]: (~r2_hidden(C_64, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_98])).
% 2.24/1.32  tff(c_126, plain, (![B_4]: (r1_xboole_0(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_10, c_117])).
% 2.24/1.32  tff(c_220, plain, (![A_71, B_72]: (k7_relat_1(A_71, B_72)=k1_xboole_0 | ~r1_xboole_0(B_72, k1_relat_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.32  tff(c_231, plain, (![A_73]: (k7_relat_1(A_73, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_126, c_220])).
% 2.24/1.32  tff(c_235, plain, (k7_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_231])).
% 2.24/1.32  tff(c_36, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.32  tff(c_61, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.32  tff(c_73, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_61])).
% 2.24/1.32  tff(c_269, plain, (![C_84, A_85, B_86]: (k7_relat_1(k7_relat_1(C_84, A_85), B_86)=k7_relat_1(C_84, k3_xboole_0(A_85, B_86)) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.24/1.32  tff(c_34, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.32  tff(c_278, plain, (k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_269, c_34])).
% 2.24/1.32  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_235, c_73, c_278])).
% 2.24/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.32  
% 2.24/1.32  Inference rules
% 2.24/1.32  ----------------------
% 2.24/1.32  #Ref     : 0
% 2.24/1.32  #Sup     : 59
% 2.24/1.32  #Fact    : 0
% 2.24/1.32  #Define  : 0
% 2.24/1.32  #Split   : 0
% 2.24/1.32  #Chain   : 0
% 2.24/1.32  #Close   : 0
% 2.24/1.32  
% 2.24/1.32  Ordering : KBO
% 2.24/1.32  
% 2.24/1.32  Simplification rules
% 2.24/1.32  ----------------------
% 2.24/1.32  #Subsume      : 4
% 2.24/1.32  #Demod        : 6
% 2.24/1.32  #Tautology    : 33
% 2.24/1.32  #SimpNegUnit  : 0
% 2.24/1.32  #BackRed      : 0
% 2.24/1.32  
% 2.24/1.32  #Partial instantiations: 0
% 2.24/1.32  #Strategies tried      : 1
% 2.24/1.32  
% 2.24/1.32  Timing (in seconds)
% 2.24/1.32  ----------------------
% 2.24/1.33  Preprocessing        : 0.34
% 2.24/1.33  Parsing              : 0.18
% 2.24/1.33  CNF conversion       : 0.02
% 2.24/1.33  Main loop            : 0.17
% 2.24/1.33  Inferencing          : 0.07
% 2.24/1.33  Reduction            : 0.05
% 2.24/1.33  Demodulation         : 0.04
% 2.24/1.33  BG Simplification    : 0.01
% 2.24/1.33  Subsumption          : 0.03
% 2.24/1.33  Abstraction          : 0.01
% 2.24/1.33  MUC search           : 0.00
% 2.24/1.33  Cooper               : 0.00
% 2.24/1.33  Total                : 0.53
% 2.24/1.33  Index Insertion      : 0.00
% 2.24/1.33  Index Deletion       : 0.00
% 2.24/1.33  Index Matching       : 0.00
% 2.24/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
