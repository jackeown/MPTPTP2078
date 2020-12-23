%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:44 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_65,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_53,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_174,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden(k4_tarski('#skF_3'(A_44,B_45,C_46),A_44),C_46)
      | ~ r2_hidden(A_44,k9_relat_1(C_46,B_45))
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_41,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ r1_xboole_0(A_21,B_22)
      | ~ r2_hidden(C_23,k3_xboole_0(A_21,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [A_8,C_23] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_23,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_41])).

tff(c_51,plain,(
    ! [C_23] : ~ r2_hidden(C_23,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_186,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden(A_44,k9_relat_1(k1_xboole_0,B_45))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_174,c_51])).

tff(c_197,plain,(
    ! [A_47,B_48] : ~ r2_hidden(A_47,k9_relat_1(k1_xboole_0,B_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_186])).

tff(c_220,plain,(
    ! [B_48] : k9_relat_1(k1_xboole_0,B_48) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_197])).

tff(c_24,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.17  
% 1.65/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.17  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.65/1.17  
% 1.65/1.17  %Foreground sorts:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Background operators:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Foreground operators:
% 1.65/1.17  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.65/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.65/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.65/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.65/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.17  
% 1.88/1.18  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.88/1.18  tff(f_65, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.88/1.18  tff(f_53, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.88/1.18  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 1.88/1.18  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.88/1.18  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.88/1.18  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.88/1.18  tff(f_68, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.88/1.18  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.18  tff(c_22, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.88/1.18  tff(c_30, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.88/1.18  tff(c_32, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_30])).
% 1.88/1.18  tff(c_174, plain, (![A_44, B_45, C_46]: (r2_hidden(k4_tarski('#skF_3'(A_44, B_45, C_46), A_44), C_46) | ~r2_hidden(A_44, k9_relat_1(C_46, B_45)) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.88/1.18  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.18  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.88/1.18  tff(c_41, plain, (![A_21, B_22, C_23]: (~r1_xboole_0(A_21, B_22) | ~r2_hidden(C_23, k3_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.18  tff(c_48, plain, (![A_8, C_23]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_41])).
% 1.88/1.18  tff(c_51, plain, (![C_23]: (~r2_hidden(C_23, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 1.88/1.18  tff(c_186, plain, (![A_44, B_45]: (~r2_hidden(A_44, k9_relat_1(k1_xboole_0, B_45)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_174, c_51])).
% 1.88/1.18  tff(c_197, plain, (![A_47, B_48]: (~r2_hidden(A_47, k9_relat_1(k1_xboole_0, B_48)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_186])).
% 1.88/1.18  tff(c_220, plain, (![B_48]: (k9_relat_1(k1_xboole_0, B_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_197])).
% 1.88/1.18  tff(c_24, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.18  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_24])).
% 1.88/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  Inference rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Ref     : 0
% 1.88/1.18  #Sup     : 42
% 1.88/1.18  #Fact    : 0
% 1.88/1.18  #Define  : 0
% 1.88/1.18  #Split   : 0
% 1.88/1.18  #Chain   : 0
% 1.88/1.18  #Close   : 0
% 1.88/1.18  
% 1.88/1.18  Ordering : KBO
% 1.88/1.18  
% 1.88/1.18  Simplification rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Subsume      : 10
% 1.88/1.18  #Demod        : 15
% 1.88/1.18  #Tautology    : 16
% 1.88/1.18  #SimpNegUnit  : 1
% 1.88/1.18  #BackRed      : 2
% 1.88/1.18  
% 1.88/1.18  #Partial instantiations: 0
% 1.88/1.18  #Strategies tried      : 1
% 1.88/1.18  
% 1.88/1.18  Timing (in seconds)
% 1.88/1.18  ----------------------
% 1.88/1.18  Preprocessing        : 0.26
% 1.88/1.18  Parsing              : 0.15
% 1.88/1.18  CNF conversion       : 0.02
% 1.88/1.18  Main loop            : 0.16
% 1.88/1.18  Inferencing          : 0.07
% 1.88/1.18  Reduction            : 0.04
% 1.88/1.18  Demodulation         : 0.03
% 1.88/1.18  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.03
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.45
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
