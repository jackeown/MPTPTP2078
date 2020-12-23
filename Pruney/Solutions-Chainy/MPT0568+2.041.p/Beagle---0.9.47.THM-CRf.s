%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:25 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  48 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_79,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_70,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_32,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_92,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(k10_relat_1(B_31,A_32),k1_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_100,plain,(
    ! [A_17,A_32] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_17),A_32),A_17)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_92])).

tff(c_105,plain,(
    ! [A_17,A_32] : r1_tarski(k10_relat_1(k6_relat_1(A_17),A_32),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_100])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_125,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,B_39)
      | ~ r2_hidden(C_40,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_129,plain,(
    ! [C_41] : ~ r2_hidden(C_41,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_125])).

tff(c_156,plain,(
    ! [B_43] : r1_tarski(k1_xboole_0,B_43) ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_170,plain,(
    ! [B_45] :
      ( k1_xboole_0 = B_45
      | ~ r1_tarski(B_45,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_156,c_14])).

tff(c_178,plain,(
    ! [A_32] : k10_relat_1(k6_relat_1(k1_xboole_0),A_32) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_170])).

tff(c_189,plain,(
    ! [A_32] : k10_relat_1(k1_xboole_0,A_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_178])).

tff(c_34,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:19:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.19  
% 1.84/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.84/1.19  
% 1.84/1.19  %Foreground sorts:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Background operators:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Foreground operators:
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.84/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.84/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.84/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.84/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.84/1.19  
% 1.84/1.20  tff(f_79, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.84/1.20  tff(f_70, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.84/1.20  tff(f_78, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.84/1.20  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.84/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.84/1.20  tff(f_68, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.84/1.20  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.84/1.20  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.84/1.20  tff(f_82, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.84/1.20  tff(c_32, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.84/1.20  tff(c_24, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.84/1.20  tff(c_28, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.84/1.20  tff(c_92, plain, (![B_31, A_32]: (r1_tarski(k10_relat_1(B_31, A_32), k1_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.84/1.20  tff(c_100, plain, (![A_17, A_32]: (r1_tarski(k10_relat_1(k6_relat_1(A_17), A_32), A_17) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_92])).
% 1.84/1.20  tff(c_105, plain, (![A_17, A_32]: (r1_tarski(k10_relat_1(k6_relat_1(A_17), A_32), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_100])).
% 1.84/1.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.84/1.20  tff(c_20, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.84/1.20  tff(c_125, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, B_39) | ~r2_hidden(C_40, A_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.20  tff(c_129, plain, (![C_41]: (~r2_hidden(C_41, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_125])).
% 1.84/1.20  tff(c_156, plain, (![B_43]: (r1_tarski(k1_xboole_0, B_43))), inference(resolution, [status(thm)], [c_6, c_129])).
% 1.84/1.20  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.20  tff(c_170, plain, (![B_45]: (k1_xboole_0=B_45 | ~r1_tarski(B_45, k1_xboole_0))), inference(resolution, [status(thm)], [c_156, c_14])).
% 1.84/1.20  tff(c_178, plain, (![A_32]: (k10_relat_1(k6_relat_1(k1_xboole_0), A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_105, c_170])).
% 1.84/1.20  tff(c_189, plain, (![A_32]: (k10_relat_1(k1_xboole_0, A_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_178])).
% 1.84/1.20  tff(c_34, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.84/1.20  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_34])).
% 1.84/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  Inference rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Ref     : 0
% 1.84/1.20  #Sup     : 38
% 1.84/1.20  #Fact    : 0
% 1.84/1.20  #Define  : 0
% 1.84/1.20  #Split   : 0
% 1.84/1.20  #Chain   : 0
% 1.84/1.20  #Close   : 0
% 1.84/1.20  
% 1.84/1.20  Ordering : KBO
% 1.84/1.20  
% 1.84/1.20  Simplification rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Subsume      : 2
% 1.84/1.20  #Demod        : 11
% 1.84/1.20  #Tautology    : 21
% 1.84/1.20  #SimpNegUnit  : 0
% 1.84/1.20  #BackRed      : 2
% 1.84/1.20  
% 1.84/1.20  #Partial instantiations: 0
% 1.84/1.20  #Strategies tried      : 1
% 1.84/1.20  
% 1.84/1.20  Timing (in seconds)
% 1.84/1.20  ----------------------
% 1.84/1.21  Preprocessing        : 0.28
% 1.84/1.21  Parsing              : 0.15
% 1.84/1.21  CNF conversion       : 0.02
% 1.84/1.21  Main loop            : 0.15
% 1.84/1.21  Inferencing          : 0.06
% 1.84/1.21  Reduction            : 0.04
% 1.84/1.21  Demodulation         : 0.03
% 1.84/1.21  BG Simplification    : 0.01
% 1.84/1.21  Subsumption          : 0.03
% 1.84/1.21  Abstraction          : 0.01
% 1.84/1.21  MUC search           : 0.00
% 1.84/1.21  Cooper               : 0.00
% 1.84/1.21  Total                : 0.45
% 1.84/1.21  Index Insertion      : 0.00
% 1.84/1.21  Index Deletion       : 0.00
% 1.84/1.21  Index Matching       : 0.00
% 1.84/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
