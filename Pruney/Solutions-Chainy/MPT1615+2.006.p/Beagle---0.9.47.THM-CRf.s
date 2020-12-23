%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:35 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   45 (  48 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  63 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_orders_2 > l1_pre_topc > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_26,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A)))))
         => k1_yellow_0(k2_yellow_1(u1_pre_topc(A)),B) = k3_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_1)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_6] : l1_orders_2(k2_yellow_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    ! [A_16] :
      ( k1_yellow_0(A_16,k1_xboole_0) = k3_yellow_0(A_16)
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_57,plain,(
    ! [A_6] : k1_yellow_0(k2_yellow_1(A_6),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_6)) ),
    inference(resolution,[status(thm)],[c_12,c_53])).

tff(c_2,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_14,plain,(
    ! [A_7] : u1_struct_0(k2_yellow_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_8,B_10] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_8)),B_10) = k3_tarski(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_8)))))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    ! [A_23,B_24] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_23)),B_24) = k3_tarski(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_pre_topc(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_76,plain,(
    ! [A_23] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_23)),k1_xboole_0) = k3_tarski(k1_xboole_0)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_79,plain,(
    ! [A_25] :
      ( k3_yellow_0(k2_yellow_1(u1_pre_topc(A_25))) = k1_xboole_0
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_2,c_76])).

tff(c_20,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_20])).

tff(c_92,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_85])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.12  
% 1.72/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.12  %$ r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_orders_2 > l1_pre_topc > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_1
% 1.72/1.12  
% 1.72/1.12  %Foreground sorts:
% 1.72/1.12  
% 1.72/1.12  
% 1.72/1.12  %Background operators:
% 1.72/1.12  
% 1.72/1.12  
% 1.72/1.12  %Foreground operators:
% 1.72/1.12  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 1.72/1.12  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.72/1.12  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 1.72/1.12  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.72/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.12  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.72/1.12  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.72/1.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.72/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.12  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.72/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.72/1.12  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 1.72/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.72/1.12  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.72/1.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.72/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.72/1.12  
% 1.72/1.13  tff(f_68, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow_1)).
% 1.72/1.13  tff(f_42, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 1.72/1.13  tff(f_38, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 1.72/1.13  tff(f_26, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.72/1.13  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.72/1.13  tff(f_46, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 1.72/1.13  tff(f_58, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A))))) => (k1_yellow_0(k2_yellow_1(u1_pre_topc(A)), B) = k3_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_yellow_1)).
% 1.72/1.13  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.72/1.13  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.72/1.13  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.72/1.13  tff(c_12, plain, (![A_6]: (l1_orders_2(k2_yellow_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.72/1.13  tff(c_53, plain, (![A_16]: (k1_yellow_0(A_16, k1_xboole_0)=k3_yellow_0(A_16) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.72/1.13  tff(c_57, plain, (![A_6]: (k1_yellow_0(k2_yellow_1(A_6), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_6)))), inference(resolution, [status(thm)], [c_12, c_53])).
% 1.72/1.13  tff(c_2, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.72/1.13  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.72/1.13  tff(c_14, plain, (![A_7]: (u1_struct_0(k2_yellow_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.72/1.13  tff(c_18, plain, (![A_8, B_10]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_8)), B_10)=k3_tarski(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_8))))) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.72/1.13  tff(c_72, plain, (![A_23, B_24]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_23)), B_24)=k3_tarski(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_pre_topc(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 1.72/1.13  tff(c_76, plain, (![A_23]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_23)), k1_xboole_0)=k3_tarski(k1_xboole_0) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_4, c_72])).
% 1.72/1.13  tff(c_79, plain, (![A_25]: (k3_yellow_0(k2_yellow_1(u1_pre_topc(A_25)))=k1_xboole_0 | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_2, c_76])).
% 1.72/1.13  tff(c_20, plain, (k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1')))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.72/1.13  tff(c_85, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_79, c_20])).
% 1.72/1.13  tff(c_92, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_85])).
% 1.72/1.13  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_92])).
% 1.72/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.13  
% 1.72/1.13  Inference rules
% 1.72/1.13  ----------------------
% 1.72/1.13  #Ref     : 0
% 1.72/1.13  #Sup     : 14
% 1.72/1.13  #Fact    : 0
% 1.72/1.13  #Define  : 0
% 1.72/1.13  #Split   : 0
% 1.72/1.13  #Chain   : 0
% 1.72/1.13  #Close   : 0
% 1.72/1.13  
% 1.72/1.13  Ordering : KBO
% 1.72/1.13  
% 1.72/1.13  Simplification rules
% 1.72/1.13  ----------------------
% 1.72/1.13  #Subsume      : 0
% 1.72/1.13  #Demod        : 5
% 1.72/1.13  #Tautology    : 9
% 1.72/1.13  #SimpNegUnit  : 1
% 1.72/1.13  #BackRed      : 0
% 1.72/1.13  
% 1.72/1.13  #Partial instantiations: 0
% 1.72/1.13  #Strategies tried      : 1
% 1.72/1.13  
% 1.72/1.13  Timing (in seconds)
% 1.72/1.13  ----------------------
% 1.72/1.14  Preprocessing        : 0.27
% 1.72/1.14  Parsing              : 0.15
% 1.72/1.14  CNF conversion       : 0.01
% 1.72/1.14  Main loop            : 0.10
% 1.72/1.14  Inferencing          : 0.04
% 1.72/1.14  Reduction            : 0.03
% 1.72/1.14  Demodulation         : 0.02
% 1.72/1.14  BG Simplification    : 0.01
% 1.72/1.14  Subsumption          : 0.01
% 1.72/1.14  Abstraction          : 0.01
% 1.72/1.14  MUC search           : 0.00
% 1.72/1.14  Cooper               : 0.00
% 1.72/1.14  Total                : 0.40
% 1.72/1.14  Index Insertion      : 0.00
% 1.72/1.14  Index Deletion       : 0.00
% 1.72/1.14  Index Matching       : 0.00
% 1.72/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
