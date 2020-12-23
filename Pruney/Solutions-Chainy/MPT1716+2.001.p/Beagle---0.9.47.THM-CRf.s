%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:40 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   35 (  48 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 130 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
              <=> k1_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k1_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [B_26,C_27,A_28] :
      ( m1_pre_topc(B_26,C_27)
      | ~ r1_tarski(u1_struct_0(B_26),u1_struct_0(C_27))
      | ~ m1_pre_topc(C_27,A_28)
      | ~ m1_pre_topc(B_26,A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_71,plain,(
    ! [B_29,A_30] :
      ( m1_pre_topc(B_29,B_29)
      | ~ m1_pre_topc(B_29,A_30)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_73,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_76,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_73])).

tff(c_86,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_tsep_1(A_34,B_35,C_36) = g1_pre_topc(u1_struct_0(C_36),u1_pre_topc(C_36))
      | ~ m1_pre_topc(B_35,C_36)
      | ~ m1_pre_topc(C_36,A_34)
      | v2_struct_0(C_36)
      | ~ m1_pre_topc(B_35,A_34)
      | v2_struct_0(B_35)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_88,plain,(
    ! [A_34] :
      ( k1_tsep_1(A_34,'#skF_2','#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',A_34)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_76,c_86])).

tff(c_97,plain,(
    ! [A_37] :
      ( k1_tsep_1(A_37,'#skF_2','#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_88])).

tff(c_101,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_97])).

tff(c_106,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_101])).

tff(c_108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_16,c_106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.17  
% 2.07/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.17  %$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1
% 2.07/1.17  
% 2.07/1.17  %Foreground sorts:
% 2.07/1.17  
% 2.07/1.17  
% 2.07/1.17  %Background operators:
% 2.07/1.17  
% 2.07/1.17  
% 2.07/1.17  %Foreground operators:
% 2.07/1.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.07/1.17  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 2.07/1.17  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.07/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.17  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.07/1.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.07/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.17  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.17  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.17  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.07/1.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.07/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.07/1.17  
% 2.07/1.18  tff(f_84, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 2.07/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.07/1.18  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.07/1.18  tff(f_54, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) <=> (k1_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 2.07/1.18  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.07/1.18  tff(c_16, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.07/1.18  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.07/1.18  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.07/1.18  tff(c_18, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.07/1.18  tff(c_20, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.07/1.18  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.18  tff(c_63, plain, (![B_26, C_27, A_28]: (m1_pre_topc(B_26, C_27) | ~r1_tarski(u1_struct_0(B_26), u1_struct_0(C_27)) | ~m1_pre_topc(C_27, A_28) | ~m1_pre_topc(B_26, A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.18  tff(c_71, plain, (![B_29, A_30]: (m1_pre_topc(B_29, B_29) | ~m1_pre_topc(B_29, A_30) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(resolution, [status(thm)], [c_6, c_63])).
% 2.07/1.18  tff(c_73, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_71])).
% 2.07/1.18  tff(c_76, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_73])).
% 2.07/1.18  tff(c_86, plain, (![A_34, B_35, C_36]: (k1_tsep_1(A_34, B_35, C_36)=g1_pre_topc(u1_struct_0(C_36), u1_pre_topc(C_36)) | ~m1_pre_topc(B_35, C_36) | ~m1_pre_topc(C_36, A_34) | v2_struct_0(C_36) | ~m1_pre_topc(B_35, A_34) | v2_struct_0(B_35) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.07/1.18  tff(c_88, plain, (![A_34]: (k1_tsep_1(A_34, '#skF_2', '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', A_34) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(resolution, [status(thm)], [c_76, c_86])).
% 2.07/1.18  tff(c_97, plain, (![A_37]: (k1_tsep_1(A_37, '#skF_2', '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', A_37) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_88])).
% 2.07/1.18  tff(c_101, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_97])).
% 2.07/1.18  tff(c_106, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_101])).
% 2.07/1.18  tff(c_108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_16, c_106])).
% 2.07/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.18  
% 2.07/1.18  Inference rules
% 2.07/1.18  ----------------------
% 2.07/1.18  #Ref     : 0
% 2.07/1.18  #Sup     : 14
% 2.07/1.18  #Fact    : 0
% 2.07/1.18  #Define  : 0
% 2.07/1.18  #Split   : 1
% 2.07/1.18  #Chain   : 0
% 2.07/1.18  #Close   : 0
% 2.07/1.18  
% 2.07/1.18  Ordering : KBO
% 2.07/1.18  
% 2.07/1.18  Simplification rules
% 2.07/1.18  ----------------------
% 2.07/1.18  #Subsume      : 1
% 2.07/1.18  #Demod        : 11
% 2.07/1.18  #Tautology    : 6
% 2.07/1.18  #SimpNegUnit  : 4
% 2.07/1.18  #BackRed      : 0
% 2.07/1.18  
% 2.07/1.18  #Partial instantiations: 0
% 2.07/1.18  #Strategies tried      : 1
% 2.07/1.18  
% 2.07/1.18  Timing (in seconds)
% 2.07/1.18  ----------------------
% 2.07/1.19  Preprocessing        : 0.28
% 2.07/1.19  Parsing              : 0.16
% 2.07/1.19  CNF conversion       : 0.02
% 2.07/1.19  Main loop            : 0.14
% 2.07/1.19  Inferencing          : 0.05
% 2.07/1.19  Reduction            : 0.04
% 2.07/1.19  Demodulation         : 0.03
% 2.07/1.19  BG Simplification    : 0.01
% 2.07/1.19  Subsumption          : 0.03
% 2.07/1.19  Abstraction          : 0.01
% 2.07/1.19  MUC search           : 0.00
% 2.07/1.19  Cooper               : 0.00
% 2.07/1.19  Total                : 0.44
% 2.07/1.19  Index Insertion      : 0.00
% 2.07/1.19  Index Deletion       : 0.00
% 2.07/1.19  Index Matching       : 0.00
% 2.07/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
