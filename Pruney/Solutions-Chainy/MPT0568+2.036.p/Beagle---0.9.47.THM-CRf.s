%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:25 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   49 (  53 expanded)
%              Number of leaves         :   32 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  48 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_86,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [A_58,B_59] :
      ( ~ r2_hidden(A_58,B_59)
      | ~ r1_xboole_0(k1_tarski(A_58),B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,(
    ! [A_58] : ~ r2_hidden(A_58,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_73])).

tff(c_91,plain,(
    ! [B_65] : r1_tarski(k1_xboole_0,B_65) ),
    inference(resolution,[status(thm)],[c_86,c_78])).

tff(c_34,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_2'(A_32),A_32)
      | v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_80,plain,(
    ! [A_63] : ~ r2_hidden(A_63,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_73])).

tff(c_85,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_80])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_103,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k10_relat_1(B_69,A_70),k1_relat_1(B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_108,plain,(
    ! [A_70] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_70),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_103])).

tff(c_112,plain,(
    ! [A_71] : r1_tarski(k10_relat_1(k1_xboole_0,A_71),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_108])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_114,plain,(
    ! [A_71] :
      ( k10_relat_1(k1_xboole_0,A_71) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k10_relat_1(k1_xboole_0,A_71)) ) ),
    inference(resolution,[status(thm)],[c_112,c_8])).

tff(c_117,plain,(
    ! [A_71] : k10_relat_1(k1_xboole_0,A_71) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_114])).

tff(c_42,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:47:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.30  
% 1.95/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 1.95/1.30  
% 1.95/1.30  %Foreground sorts:
% 1.95/1.30  
% 1.95/1.30  
% 1.95/1.30  %Background operators:
% 1.95/1.30  
% 1.95/1.30  
% 1.95/1.30  %Foreground operators:
% 1.95/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.95/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.95/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.95/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.95/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.95/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.95/1.30  
% 2.10/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.10/1.31  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.10/1.31  tff(f_57, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.10/1.31  tff(f_67, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.10/1.31  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.10/1.31  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.10/1.31  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.10/1.31  tff(f_77, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.10/1.31  tff(c_86, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.31  tff(c_14, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.10/1.31  tff(c_73, plain, (![A_58, B_59]: (~r2_hidden(A_58, B_59) | ~r1_xboole_0(k1_tarski(A_58), B_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.10/1.31  tff(c_78, plain, (![A_58]: (~r2_hidden(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_73])).
% 2.10/1.31  tff(c_91, plain, (![B_65]: (r1_tarski(k1_xboole_0, B_65))), inference(resolution, [status(thm)], [c_86, c_78])).
% 2.10/1.31  tff(c_34, plain, (![A_32]: (r2_hidden('#skF_2'(A_32), A_32) | v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.31  tff(c_80, plain, (![A_63]: (~r2_hidden(A_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_73])).
% 2.10/1.31  tff(c_85, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_80])).
% 2.10/1.31  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.10/1.31  tff(c_103, plain, (![B_69, A_70]: (r1_tarski(k10_relat_1(B_69, A_70), k1_relat_1(B_69)) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.31  tff(c_108, plain, (![A_70]: (r1_tarski(k10_relat_1(k1_xboole_0, A_70), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_103])).
% 2.10/1.31  tff(c_112, plain, (![A_71]: (r1_tarski(k10_relat_1(k1_xboole_0, A_71), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_108])).
% 2.10/1.31  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.31  tff(c_114, plain, (![A_71]: (k10_relat_1(k1_xboole_0, A_71)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k10_relat_1(k1_xboole_0, A_71)))), inference(resolution, [status(thm)], [c_112, c_8])).
% 2.10/1.31  tff(c_117, plain, (![A_71]: (k10_relat_1(k1_xboole_0, A_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_114])).
% 2.10/1.31  tff(c_42, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.10/1.31  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_42])).
% 2.10/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.31  
% 2.10/1.31  Inference rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Ref     : 0
% 2.10/1.31  #Sup     : 16
% 2.10/1.31  #Fact    : 0
% 2.10/1.31  #Define  : 0
% 2.10/1.31  #Split   : 0
% 2.10/1.31  #Chain   : 0
% 2.10/1.31  #Close   : 0
% 2.10/1.31  
% 2.10/1.31  Ordering : KBO
% 2.10/1.31  
% 2.10/1.31  Simplification rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Subsume      : 0
% 2.10/1.31  #Demod        : 7
% 2.10/1.31  #Tautology    : 11
% 2.10/1.31  #SimpNegUnit  : 0
% 2.10/1.31  #BackRed      : 2
% 2.10/1.31  
% 2.10/1.31  #Partial instantiations: 0
% 2.10/1.31  #Strategies tried      : 1
% 2.10/1.31  
% 2.10/1.31  Timing (in seconds)
% 2.10/1.31  ----------------------
% 2.10/1.31  Preprocessing        : 0.35
% 2.10/1.31  Parsing              : 0.16
% 2.10/1.31  CNF conversion       : 0.03
% 2.10/1.32  Main loop            : 0.13
% 2.10/1.32  Inferencing          : 0.04
% 2.10/1.32  Reduction            : 0.04
% 2.10/1.32  Demodulation         : 0.03
% 2.10/1.32  BG Simplification    : 0.02
% 2.10/1.32  Subsumption          : 0.02
% 2.10/1.32  Abstraction          : 0.02
% 2.10/1.32  MUC search           : 0.00
% 2.10/1.32  Cooper               : 0.00
% 2.10/1.32  Total                : 0.51
% 2.10/1.32  Index Insertion      : 0.00
% 2.10/1.32  Index Deletion       : 0.00
% 2.10/1.32  Index Matching       : 0.00
% 2.10/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
