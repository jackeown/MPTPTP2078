%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:33 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   45 (  53 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  60 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_52,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_75,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),B_30)
      | r2_hidden('#skF_2'(A_29,B_30),A_29)
      | B_30 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ r1_xboole_0(A_21,B_22)
      | ~ r2_hidden(C_23,k3_xboole_0(A_21,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    ! [A_9,C_23] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_23,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_63,plain,(
    ! [C_23] : ~ r2_hidden(C_23,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_61])).

tff(c_97,plain,(
    ! [B_30] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_30),B_30)
      | k1_xboole_0 = B_30 ) ),
    inference(resolution,[status(thm)],[c_75,c_63])).

tff(c_32,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_43,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_43])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_177,plain,(
    ! [A_43,B_44,C_45] :
      ( r2_hidden('#skF_4'(A_43,B_44,C_45),k2_relat_1(C_45))
      | ~ r2_hidden(A_43,k10_relat_1(C_45,B_44))
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_180,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_4'(A_43,B_44,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_43,k10_relat_1(k1_xboole_0,B_44))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_177])).

tff(c_182,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_4'(A_43,B_44,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_43,k10_relat_1(k1_xboole_0,B_44)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_180])).

tff(c_184,plain,(
    ! [A_46,B_47] : ~ r2_hidden(A_46,k10_relat_1(k1_xboole_0,B_47)) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_182])).

tff(c_207,plain,(
    ! [B_47] : k10_relat_1(k1_xboole_0,B_47) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_184])).

tff(c_34,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.16  
% 1.84/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.16  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 1.84/1.16  
% 1.84/1.16  %Foreground sorts:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Background operators:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Foreground operators:
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.84/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.84/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.84/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.84/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.84/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.84/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.84/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.84/1.16  
% 1.84/1.17  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.84/1.17  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.84/1.17  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.84/1.17  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.84/1.17  tff(f_67, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.84/1.17  tff(f_52, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.84/1.17  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.84/1.17  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.84/1.17  tff(f_70, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.84/1.17  tff(c_75, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), B_30) | r2_hidden('#skF_2'(A_29, B_30), A_29) | B_30=A_29)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.84/1.17  tff(c_16, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.17  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.84/1.17  tff(c_58, plain, (![A_21, B_22, C_23]: (~r1_xboole_0(A_21, B_22) | ~r2_hidden(C_23, k3_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.17  tff(c_61, plain, (![A_9, C_23]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_58])).
% 1.84/1.17  tff(c_63, plain, (![C_23]: (~r2_hidden(C_23, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_61])).
% 1.84/1.17  tff(c_97, plain, (![B_30]: (r2_hidden('#skF_1'(k1_xboole_0, B_30), B_30) | k1_xboole_0=B_30)), inference(resolution, [status(thm)], [c_75, c_63])).
% 1.84/1.17  tff(c_32, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.84/1.17  tff(c_43, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.84/1.17  tff(c_45, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_43])).
% 1.84/1.17  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.84/1.17  tff(c_177, plain, (![A_43, B_44, C_45]: (r2_hidden('#skF_4'(A_43, B_44, C_45), k2_relat_1(C_45)) | ~r2_hidden(A_43, k10_relat_1(C_45, B_44)) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.84/1.17  tff(c_180, plain, (![A_43, B_44]: (r2_hidden('#skF_4'(A_43, B_44, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_43, k10_relat_1(k1_xboole_0, B_44)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_177])).
% 1.84/1.17  tff(c_182, plain, (![A_43, B_44]: (r2_hidden('#skF_4'(A_43, B_44, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_43, k10_relat_1(k1_xboole_0, B_44)))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_180])).
% 1.84/1.17  tff(c_184, plain, (![A_46, B_47]: (~r2_hidden(A_46, k10_relat_1(k1_xboole_0, B_47)))), inference(negUnitSimplification, [status(thm)], [c_63, c_182])).
% 1.84/1.17  tff(c_207, plain, (![B_47]: (k10_relat_1(k1_xboole_0, B_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_184])).
% 1.84/1.17  tff(c_34, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.84/1.17  tff(c_213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_34])).
% 1.84/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  Inference rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Ref     : 0
% 1.84/1.17  #Sup     : 36
% 1.84/1.17  #Fact    : 0
% 1.84/1.17  #Define  : 0
% 1.84/1.17  #Split   : 0
% 1.84/1.17  #Chain   : 0
% 1.84/1.17  #Close   : 0
% 1.84/1.17  
% 1.84/1.17  Ordering : KBO
% 1.84/1.17  
% 1.84/1.17  Simplification rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Subsume      : 6
% 1.84/1.17  #Demod        : 6
% 1.84/1.17  #Tautology    : 14
% 1.84/1.17  #SimpNegUnit  : 1
% 1.84/1.17  #BackRed      : 2
% 1.84/1.17  
% 1.84/1.17  #Partial instantiations: 0
% 1.84/1.17  #Strategies tried      : 1
% 1.84/1.17  
% 1.84/1.17  Timing (in seconds)
% 1.84/1.17  ----------------------
% 1.95/1.18  Preprocessing        : 0.27
% 1.95/1.18  Parsing              : 0.15
% 1.95/1.18  CNF conversion       : 0.02
% 1.95/1.18  Main loop            : 0.16
% 1.95/1.18  Inferencing          : 0.07
% 1.95/1.18  Reduction            : 0.04
% 1.95/1.18  Demodulation         : 0.03
% 1.95/1.18  BG Simplification    : 0.01
% 1.95/1.18  Subsumption          : 0.02
% 1.95/1.18  Abstraction          : 0.01
% 1.95/1.18  MUC search           : 0.00
% 1.95/1.18  Cooper               : 0.00
% 1.95/1.18  Total                : 0.45
% 1.95/1.18  Index Insertion      : 0.00
% 1.95/1.18  Index Deletion       : 0.00
% 1.95/1.18  Index Matching       : 0.00
% 1.95/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
