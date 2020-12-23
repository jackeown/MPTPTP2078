%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:35 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  81 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_pre_topc > k3_yellow_0 > k2_yellow_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_16,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_5))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_13] :
      ( k3_yellow_0(k2_yellow_1(A_13)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_39,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1'))
    | v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_41,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_44,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_41])).

tff(c_48,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_44])).

tff(c_49,plain,(
    v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    u1_pre_topc('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_2])).

tff(c_22,plain,(
    ! [A_11] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_11))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( ~ r1_tarski(B_4,A_3)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [A_11] :
      ( ~ r1_tarski(u1_pre_topc(A_11),k1_xboole_0)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_6])).

tff(c_60,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_26])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_4,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.23  
% 1.86/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.23  %$ r2_hidden > r1_tarski > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_pre_topc > k3_yellow_0 > k2_yellow_1 > k1_xboole_0 > #skF_1
% 1.86/1.23  
% 1.86/1.23  %Foreground sorts:
% 1.86/1.23  
% 1.86/1.23  
% 1.86/1.23  %Background operators:
% 1.86/1.23  
% 1.86/1.23  
% 1.86/1.23  %Foreground operators:
% 1.86/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.86/1.23  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.86/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.23  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.86/1.23  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.86/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.86/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.86/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.86/1.23  
% 1.86/1.24  tff(f_59, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow_1)).
% 1.86/1.24  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.86/1.24  tff(f_42, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => r2_hidden(k1_xboole_0, u1_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_pre_topc)).
% 1.86/1.24  tff(f_49, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.86/1.24  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.86/1.24  tff(f_36, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.86/1.24  tff(c_16, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.24  tff(c_14, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.24  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.24  tff(c_8, plain, (![A_5]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_5)) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.86/1.24  tff(c_28, plain, (![A_13]: (k3_yellow_0(k2_yellow_1(A_13))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.86/1.24  tff(c_12, plain, (k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1')))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.24  tff(c_39, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_1')) | v1_xboole_0(u1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_12])).
% 1.86/1.24  tff(c_41, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_39])).
% 1.86/1.24  tff(c_44, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_41])).
% 1.86/1.24  tff(c_48, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_44])).
% 1.86/1.24  tff(c_49, plain, (v1_xboole_0(u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_39])).
% 1.86/1.24  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.24  tff(c_54, plain, (u1_pre_topc('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_49, c_2])).
% 1.86/1.24  tff(c_22, plain, (![A_11]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_11)) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.86/1.24  tff(c_6, plain, (![B_4, A_3]: (~r1_tarski(B_4, A_3) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.86/1.24  tff(c_26, plain, (![A_11]: (~r1_tarski(u1_pre_topc(A_11), k1_xboole_0) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(resolution, [status(thm)], [c_22, c_6])).
% 1.86/1.24  tff(c_60, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_54, c_26])).
% 1.86/1.24  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_4, c_60])).
% 1.86/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.24  
% 1.86/1.24  Inference rules
% 1.86/1.24  ----------------------
% 1.86/1.24  #Ref     : 0
% 1.86/1.24  #Sup     : 10
% 1.86/1.24  #Fact    : 0
% 1.86/1.24  #Define  : 0
% 1.86/1.24  #Split   : 1
% 1.86/1.24  #Chain   : 0
% 1.86/1.24  #Close   : 0
% 1.86/1.24  
% 1.86/1.24  Ordering : KBO
% 1.86/1.24  
% 1.86/1.24  Simplification rules
% 1.86/1.24  ----------------------
% 1.86/1.24  #Subsume      : 0
% 1.86/1.24  #Demod        : 7
% 1.86/1.24  #Tautology    : 3
% 1.86/1.24  #SimpNegUnit  : 0
% 1.86/1.24  #BackRed      : 2
% 1.86/1.24  
% 1.86/1.24  #Partial instantiations: 0
% 1.86/1.24  #Strategies tried      : 1
% 1.86/1.24  
% 1.86/1.24  Timing (in seconds)
% 1.86/1.24  ----------------------
% 1.86/1.24  Preprocessing        : 0.28
% 1.86/1.24  Parsing              : 0.16
% 1.86/1.24  CNF conversion       : 0.02
% 1.86/1.24  Main loop            : 0.11
% 1.86/1.24  Inferencing          : 0.05
% 1.86/1.24  Reduction            : 0.03
% 1.86/1.24  Demodulation         : 0.02
% 1.86/1.24  BG Simplification    : 0.01
% 1.86/1.24  Subsumption          : 0.02
% 1.86/1.24  Abstraction          : 0.00
% 1.86/1.24  MUC search           : 0.00
% 1.86/1.24  Cooper               : 0.00
% 1.86/1.24  Total                : 0.41
% 1.86/1.24  Index Insertion      : 0.00
% 1.86/1.24  Index Deletion       : 0.00
% 1.86/1.24  Index Matching       : 0.00
% 1.86/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
