%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:31 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   42 (  44 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  61 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

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

tff(f_72,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_64,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_41,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_43,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_41])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_51,plain,(
    ! [B_19,A_20] :
      ( r1_tarski(k10_relat_1(B_19,A_20),k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    ! [A_20] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_20),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_51])).

tff(c_56,plain,(
    ! [A_20] : r1_tarski(k10_relat_1(k1_xboole_0,A_20),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_54])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_67,plain,(
    ! [C_29,B_30,A_31] :
      ( r2_hidden(C_29,B_30)
      | ~ r2_hidden(C_29,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [A_39,B_40,B_41] :
      ( r2_hidden('#skF_2'(A_39,B_40),B_41)
      | ~ r1_tarski(A_39,B_41)
      | r1_xboole_0(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_14,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_77,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r2_hidden(C_34,B_33)
      | ~ r2_hidden(C_34,A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    ! [C_34] : ~ r2_hidden(C_34,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_128,plain,(
    ! [A_42,B_43] :
      ( ~ r1_tarski(A_42,k1_xboole_0)
      | r1_xboole_0(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_119,c_80])).

tff(c_16,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_137,plain,(
    ! [B_44] :
      ( k1_xboole_0 = B_44
      | ~ r1_tarski(B_44,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_128,c_16])).

tff(c_153,plain,(
    ! [A_20] : k10_relat_1(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_137])).

tff(c_28,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.91/1.18  
% 1.91/1.18  %Foreground sorts:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Background operators:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Foreground operators:
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.91/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.18  
% 1.91/1.19  tff(f_72, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.91/1.19  tff(f_64, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.91/1.19  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.91/1.19  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.91/1.19  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.91/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.91/1.19  tff(f_62, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.91/1.19  tff(f_75, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.91/1.19  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.91/1.19  tff(c_41, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.91/1.19  tff(c_43, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_41])).
% 1.91/1.19  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.91/1.19  tff(c_51, plain, (![B_19, A_20]: (r1_tarski(k10_relat_1(B_19, A_20), k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.91/1.19  tff(c_54, plain, (![A_20]: (r1_tarski(k10_relat_1(k1_xboole_0, A_20), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_51])).
% 1.91/1.19  tff(c_56, plain, (![A_20]: (r1_tarski(k10_relat_1(k1_xboole_0, A_20), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_54])).
% 1.91/1.19  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.19  tff(c_67, plain, (![C_29, B_30, A_31]: (r2_hidden(C_29, B_30) | ~r2_hidden(C_29, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.19  tff(c_119, plain, (![A_39, B_40, B_41]: (r2_hidden('#skF_2'(A_39, B_40), B_41) | ~r1_tarski(A_39, B_41) | r1_xboole_0(A_39, B_40))), inference(resolution, [status(thm)], [c_12, c_67])).
% 1.91/1.19  tff(c_14, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.19  tff(c_77, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r2_hidden(C_34, B_33) | ~r2_hidden(C_34, A_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.19  tff(c_80, plain, (![C_34]: (~r2_hidden(C_34, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_77])).
% 1.91/1.19  tff(c_128, plain, (![A_42, B_43]: (~r1_tarski(A_42, k1_xboole_0) | r1_xboole_0(A_42, B_43))), inference(resolution, [status(thm)], [c_119, c_80])).
% 1.91/1.19  tff(c_16, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.19  tff(c_137, plain, (![B_44]: (k1_xboole_0=B_44 | ~r1_tarski(B_44, k1_xboole_0))), inference(resolution, [status(thm)], [c_128, c_16])).
% 1.91/1.19  tff(c_153, plain, (![A_20]: (k10_relat_1(k1_xboole_0, A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_137])).
% 1.91/1.19  tff(c_28, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.19  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_28])).
% 1.91/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  Inference rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Ref     : 0
% 1.91/1.19  #Sup     : 28
% 1.91/1.19  #Fact    : 0
% 1.91/1.19  #Define  : 0
% 1.91/1.19  #Split   : 0
% 1.91/1.19  #Chain   : 0
% 1.91/1.19  #Close   : 0
% 1.91/1.19  
% 1.91/1.19  Ordering : KBO
% 1.91/1.19  
% 1.91/1.19  Simplification rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Subsume      : 2
% 1.91/1.19  #Demod        : 5
% 1.91/1.19  #Tautology    : 13
% 1.91/1.19  #SimpNegUnit  : 0
% 1.91/1.19  #BackRed      : 2
% 1.91/1.19  
% 1.91/1.19  #Partial instantiations: 0
% 1.91/1.19  #Strategies tried      : 1
% 1.91/1.19  
% 1.91/1.19  Timing (in seconds)
% 1.91/1.19  ----------------------
% 1.91/1.20  Preprocessing        : 0.29
% 1.91/1.20  Parsing              : 0.16
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.14
% 1.91/1.20  Inferencing          : 0.06
% 1.91/1.20  Reduction            : 0.04
% 1.91/1.20  Demodulation         : 0.03
% 1.91/1.20  BG Simplification    : 0.01
% 1.91/1.20  Subsumption          : 0.02
% 1.91/1.20  Abstraction          : 0.00
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.45
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.20  Index Deletion       : 0.00
% 1.91/1.20  Index Matching       : 0.00
% 1.91/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
