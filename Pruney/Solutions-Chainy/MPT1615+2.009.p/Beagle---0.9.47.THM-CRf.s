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
% DateTime   : Thu Dec  3 10:25:35 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   46 (  50 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  69 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_orders_2 > l1_pre_topc > l1_orders_2 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_67,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_4] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_4))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [A_6] : l1_orders_2(k2_yellow_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_8] : u1_struct_0(k2_yellow_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_55,plain,(
    ! [A_16] :
      ( m1_subset_1(k3_yellow_0(A_16),u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_61,plain,(
    ! [A_8] :
      ( m1_subset_1(k3_yellow_0(k2_yellow_1(A_8)),A_8)
      | ~ l1_orders_2(k2_yellow_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_55])).

tff(c_65,plain,(
    ! [A_17] : m1_subset_1(k3_yellow_0(k2_yellow_1(A_17)),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_61])).

tff(c_10,plain,(
    ! [B_3,A_2] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,A_2)
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_70,plain,(
    ! [A_18] :
      ( v1_xboole_0(k3_yellow_0(k2_yellow_1(A_18)))
      | ~ v1_xboole_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_65,c_10])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_19] :
      ( k3_yellow_0(k2_yellow_1(A_19)) = k1_xboole_0
      | ~ v1_xboole_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_26,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_97,plain,(
    ~ v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_26])).

tff(c_184,plain,(
    ! [A_36] :
      ( k3_yellow_0(k2_yellow_1(A_36)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_202,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1'))
    | v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_26])).

tff(c_216,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_202])).

tff(c_221,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_216])).

tff(c_228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:25:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.19  
% 1.99/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.19  %$ r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_orders_2 > l1_pre_topc > l1_orders_2 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1
% 1.99/1.19  
% 1.99/1.19  %Foreground sorts:
% 1.99/1.19  
% 1.99/1.19  
% 1.99/1.19  %Background operators:
% 1.99/1.19  
% 1.99/1.19  
% 1.99/1.19  %Foreground operators:
% 1.99/1.19  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 1.99/1.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.99/1.19  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.19  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.99/1.19  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.99/1.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.99/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.19  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.19  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.99/1.19  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.99/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.19  
% 1.99/1.20  tff(f_77, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_1)).
% 1.99/1.20  tff(f_48, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => r2_hidden(k1_xboole_0, u1_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_pre_topc)).
% 1.99/1.20  tff(f_56, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 1.99/1.20  tff(f_67, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 1.99/1.20  tff(f_52, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 1.99/1.20  tff(f_42, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.99/1.20  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.99/1.20  tff(f_63, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.99/1.20  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.99/1.20  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.99/1.20  tff(c_12, plain, (![A_4]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_4)) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.99/1.20  tff(c_18, plain, (![A_6]: (l1_orders_2(k2_yellow_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.20  tff(c_22, plain, (![A_8]: (u1_struct_0(k2_yellow_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.99/1.20  tff(c_55, plain, (![A_16]: (m1_subset_1(k3_yellow_0(A_16), u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.20  tff(c_61, plain, (![A_8]: (m1_subset_1(k3_yellow_0(k2_yellow_1(A_8)), A_8) | ~l1_orders_2(k2_yellow_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_55])).
% 1.99/1.20  tff(c_65, plain, (![A_17]: (m1_subset_1(k3_yellow_0(k2_yellow_1(A_17)), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_61])).
% 1.99/1.20  tff(c_10, plain, (![B_3, A_2]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, A_2) | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.20  tff(c_70, plain, (![A_18]: (v1_xboole_0(k3_yellow_0(k2_yellow_1(A_18))) | ~v1_xboole_0(A_18))), inference(resolution, [status(thm)], [c_65, c_10])).
% 1.99/1.20  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.20  tff(c_75, plain, (![A_19]: (k3_yellow_0(k2_yellow_1(A_19))=k1_xboole_0 | ~v1_xboole_0(A_19))), inference(resolution, [status(thm)], [c_70, c_2])).
% 1.99/1.20  tff(c_26, plain, (k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1')))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.99/1.20  tff(c_97, plain, (~v1_xboole_0(u1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_26])).
% 1.99/1.20  tff(c_184, plain, (![A_36]: (k3_yellow_0(k2_yellow_1(A_36))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.99/1.20  tff(c_202, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_1')) | v1_xboole_0(u1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_26])).
% 1.99/1.20  tff(c_216, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_97, c_202])).
% 1.99/1.20  tff(c_221, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_216])).
% 1.99/1.20  tff(c_228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_221])).
% 1.99/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  Inference rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Ref     : 0
% 1.99/1.20  #Sup     : 39
% 1.99/1.20  #Fact    : 0
% 1.99/1.20  #Define  : 0
% 1.99/1.20  #Split   : 1
% 1.99/1.20  #Chain   : 0
% 1.99/1.20  #Close   : 0
% 1.99/1.20  
% 1.99/1.20  Ordering : KBO
% 1.99/1.20  
% 1.99/1.20  Simplification rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Subsume      : 16
% 1.99/1.20  #Demod        : 14
% 1.99/1.20  #Tautology    : 18
% 1.99/1.20  #SimpNegUnit  : 8
% 1.99/1.20  #BackRed      : 0
% 1.99/1.20  
% 1.99/1.20  #Partial instantiations: 0
% 1.99/1.20  #Strategies tried      : 1
% 1.99/1.20  
% 1.99/1.20  Timing (in seconds)
% 1.99/1.20  ----------------------
% 1.99/1.20  Preprocessing        : 0.27
% 1.99/1.20  Parsing              : 0.15
% 1.99/1.20  CNF conversion       : 0.02
% 1.99/1.20  Main loop            : 0.17
% 1.99/1.20  Inferencing          : 0.07
% 1.99/1.20  Reduction            : 0.04
% 1.99/1.20  Demodulation         : 0.03
% 1.99/1.20  BG Simplification    : 0.01
% 1.99/1.20  Subsumption          : 0.03
% 1.99/1.20  Abstraction          : 0.01
% 1.99/1.20  MUC search           : 0.00
% 1.99/1.21  Cooper               : 0.00
% 1.99/1.21  Total                : 0.46
% 1.99/1.21  Index Insertion      : 0.00
% 1.99/1.21  Index Deletion       : 0.00
% 1.99/1.21  Index Matching       : 0.00
% 1.99/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
