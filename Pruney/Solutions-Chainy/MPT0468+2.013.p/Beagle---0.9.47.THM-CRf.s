%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:50 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_142,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(k4_tarski('#skF_3'(A_70,B_71),'#skF_4'(A_70,B_71)),A_70)
      | r1_tarski(A_70,B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [B_31,C_32] : ~ r2_hidden(k4_tarski(B_31,C_32),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_156,plain,(
    ! [B_71] :
      ( r1_tarski('#skF_5',B_71)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_142,c_26])).

tff(c_164,plain,(
    ! [B_72] : r1_tarski('#skF_5',B_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_156])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_2'(A_50),B_51)
      | ~ r1_tarski(A_50,B_51)
      | k1_xboole_0 = A_50 ) ),
    inference(resolution,[status(thm)],[c_8,c_60])).

tff(c_14,plain,(
    ! [C_11,B_10] : ~ r2_hidden(C_11,k4_xboole_0(B_10,k1_tarski(C_11))) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_80,plain,(
    ! [A_50,B_10] :
      ( ~ r1_tarski(A_50,k4_xboole_0(B_10,k1_tarski('#skF_2'(A_50))))
      | k1_xboole_0 = A_50 ) ),
    inference(resolution,[status(thm)],[c_67,c_14])).

tff(c_176,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_164,c_80])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.23  
% 1.88/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.23  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 1.88/1.23  
% 1.88/1.23  %Foreground sorts:
% 1.88/1.23  
% 1.88/1.23  
% 1.88/1.23  %Background operators:
% 1.88/1.23  
% 1.88/1.23  
% 1.88/1.23  %Foreground operators:
% 1.88/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.88/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.88/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.88/1.23  
% 1.88/1.24  tff(f_68, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 1.88/1.24  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 1.88/1.24  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.88/1.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.88/1.24  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.88/1.24  tff(c_24, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.24  tff(c_28, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.24  tff(c_142, plain, (![A_70, B_71]: (r2_hidden(k4_tarski('#skF_3'(A_70, B_71), '#skF_4'(A_70, B_71)), A_70) | r1_tarski(A_70, B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.88/1.24  tff(c_26, plain, (![B_31, C_32]: (~r2_hidden(k4_tarski(B_31, C_32), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.24  tff(c_156, plain, (![B_71]: (r1_tarski('#skF_5', B_71) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_142, c_26])).
% 1.88/1.24  tff(c_164, plain, (![B_72]: (r1_tarski('#skF_5', B_72))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_156])).
% 1.88/1.24  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.88/1.24  tff(c_60, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.24  tff(c_67, plain, (![A_50, B_51]: (r2_hidden('#skF_2'(A_50), B_51) | ~r1_tarski(A_50, B_51) | k1_xboole_0=A_50)), inference(resolution, [status(thm)], [c_8, c_60])).
% 1.88/1.24  tff(c_14, plain, (![C_11, B_10]: (~r2_hidden(C_11, k4_xboole_0(B_10, k1_tarski(C_11))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.88/1.24  tff(c_80, plain, (![A_50, B_10]: (~r1_tarski(A_50, k4_xboole_0(B_10, k1_tarski('#skF_2'(A_50)))) | k1_xboole_0=A_50)), inference(resolution, [status(thm)], [c_67, c_14])).
% 1.88/1.24  tff(c_176, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_164, c_80])).
% 1.88/1.24  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_176])).
% 1.88/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.24  
% 1.88/1.24  Inference rules
% 1.88/1.24  ----------------------
% 1.88/1.24  #Ref     : 0
% 1.88/1.24  #Sup     : 29
% 1.88/1.24  #Fact    : 0
% 1.88/1.24  #Define  : 0
% 1.88/1.24  #Split   : 0
% 1.88/1.24  #Chain   : 0
% 1.88/1.24  #Close   : 0
% 1.88/1.24  
% 1.88/1.24  Ordering : KBO
% 1.88/1.24  
% 1.88/1.24  Simplification rules
% 1.88/1.24  ----------------------
% 1.88/1.24  #Subsume      : 2
% 1.88/1.24  #Demod        : 3
% 1.88/1.24  #Tautology    : 7
% 1.88/1.24  #SimpNegUnit  : 2
% 1.88/1.24  #BackRed      : 0
% 1.88/1.24  
% 1.88/1.24  #Partial instantiations: 0
% 1.88/1.24  #Strategies tried      : 1
% 1.88/1.24  
% 1.88/1.24  Timing (in seconds)
% 1.88/1.24  ----------------------
% 1.88/1.24  Preprocessing        : 0.27
% 1.88/1.24  Parsing              : 0.14
% 1.88/1.24  CNF conversion       : 0.02
% 1.88/1.24  Main loop            : 0.15
% 1.88/1.24  Inferencing          : 0.06
% 1.88/1.24  Reduction            : 0.04
% 1.88/1.24  Demodulation         : 0.03
% 1.88/1.24  BG Simplification    : 0.01
% 1.88/1.24  Subsumption          : 0.03
% 1.88/1.24  Abstraction          : 0.01
% 1.88/1.24  MUC search           : 0.00
% 1.88/1.24  Cooper               : 0.00
% 1.88/1.25  Total                : 0.44
% 1.88/1.25  Index Insertion      : 0.00
% 1.88/1.25  Index Deletion       : 0.00
% 1.88/1.25  Index Matching       : 0.00
% 1.88/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
