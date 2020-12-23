%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:46 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 136 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r3_lattice3 > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(a_2_1_lattice3,type,(
    a_2_1_lattice3: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( r3_lattice3(A,B,C)
               => r3_lattices(A,B,k16_lattice3(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_1_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

tff(f_33,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] : k16_lattice3(A,B) = k15_lattice3(A,a_2_1_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r2_hidden(B,C)
             => ( r3_lattices(A,B,k15_lattice3(A,C))
                & r3_lattices(A,k16_lattice3(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    r3_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [D_9,B_5,C_6] :
      ( r2_hidden(D_9,a_2_1_lattice3(B_5,C_6))
      | ~ r3_lattice3(B_5,D_9,C_6)
      | ~ m1_subset_1(D_9,u1_struct_0(B_5))
      | ~ l3_lattices(B_5)
      | v2_struct_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    v4_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k15_lattice3(A_1,a_2_1_lattice3(A_1,B_3)) = k16_lattice3(A_1,B_3)
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [A_41,B_42,C_43] :
      ( r3_lattices(A_41,B_42,k15_lattice3(A_41,C_43))
      | ~ r2_hidden(B_42,C_43)
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l3_lattices(A_41)
      | ~ v4_lattice3(A_41)
      | ~ v10_lattices(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_77,plain,(
    ! [A_44,B_45,B_46] :
      ( r3_lattices(A_44,B_45,k16_lattice3(A_44,B_46))
      | ~ r2_hidden(B_45,a_2_1_lattice3(A_44,B_46))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l3_lattices(A_44)
      | ~ v4_lattice3(A_44)
      | ~ v10_lattices(A_44)
      | v2_struct_0(A_44)
      | ~ l3_lattices(A_44)
      | v2_struct_0(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_16,plain,(
    ~ r3_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_80,plain,
    ( ~ r2_hidden('#skF_3',a_2_1_lattice3('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v4_lattice3('#skF_2')
    | ~ v10_lattices('#skF_2')
    | ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_16])).

tff(c_83,plain,
    ( ~ r2_hidden('#skF_3',a_2_1_lattice3('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_24,c_20,c_80])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_3',a_2_1_lattice3('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_83])).

tff(c_87,plain,
    ( ~ r3_lattice3('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_84])).

tff(c_90,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_87])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:07:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.18  %$ r3_lattices > r3_lattice3 > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.69/1.18  
% 1.69/1.18  %Foreground sorts:
% 1.69/1.18  
% 1.69/1.18  
% 1.69/1.18  %Background operators:
% 1.69/1.18  
% 1.69/1.18  
% 1.69/1.18  %Foreground operators:
% 1.69/1.18  tff(l3_lattices, type, l3_lattices: $i > $o).
% 1.69/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.69/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.69/1.18  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.18  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 1.69/1.18  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 1.69/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.18  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 1.69/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.18  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 1.69/1.18  tff(v10_lattices, type, v10_lattices: $i > $o).
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.69/1.18  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 1.69/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.69/1.18  
% 1.93/1.19  tff(f_84, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattice3)).
% 1.93/1.19  tff(f_47, axiom, (![A, B, C]: ((~v2_struct_0(B) & l3_lattices(B)) => (r2_hidden(A, a_2_1_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 1.93/1.19  tff(f_33, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (k16_lattice3(A, B) = k15_lattice3(A, a_2_1_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d22_lattice3)).
% 1.93/1.19  tff(f_66, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 1.93/1.19  tff(c_28, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.93/1.19  tff(c_22, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.93/1.19  tff(c_20, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.93/1.19  tff(c_18, plain, (r3_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.93/1.19  tff(c_4, plain, (![D_9, B_5, C_6]: (r2_hidden(D_9, a_2_1_lattice3(B_5, C_6)) | ~r3_lattice3(B_5, D_9, C_6) | ~m1_subset_1(D_9, u1_struct_0(B_5)) | ~l3_lattices(B_5) | v2_struct_0(B_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.19  tff(c_26, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.93/1.19  tff(c_24, plain, (v4_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.93/1.19  tff(c_2, plain, (![A_1, B_3]: (k15_lattice3(A_1, a_2_1_lattice3(A_1, B_3))=k16_lattice3(A_1, B_3) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.19  tff(c_73, plain, (![A_41, B_42, C_43]: (r3_lattices(A_41, B_42, k15_lattice3(A_41, C_43)) | ~r2_hidden(B_42, C_43) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l3_lattices(A_41) | ~v4_lattice3(A_41) | ~v10_lattices(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.93/1.19  tff(c_77, plain, (![A_44, B_45, B_46]: (r3_lattices(A_44, B_45, k16_lattice3(A_44, B_46)) | ~r2_hidden(B_45, a_2_1_lattice3(A_44, B_46)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l3_lattices(A_44) | ~v4_lattice3(A_44) | ~v10_lattices(A_44) | v2_struct_0(A_44) | ~l3_lattices(A_44) | v2_struct_0(A_44))), inference(superposition, [status(thm), theory('equality')], [c_2, c_73])).
% 1.93/1.19  tff(c_16, plain, (~r3_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.93/1.19  tff(c_80, plain, (~r2_hidden('#skF_3', a_2_1_lattice3('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v4_lattice3('#skF_2') | ~v10_lattices('#skF_2') | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_77, c_16])).
% 1.93/1.19  tff(c_83, plain, (~r2_hidden('#skF_3', a_2_1_lattice3('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26, c_24, c_20, c_80])).
% 1.93/1.19  tff(c_84, plain, (~r2_hidden('#skF_3', a_2_1_lattice3('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_28, c_83])).
% 1.93/1.19  tff(c_87, plain, (~r3_lattice3('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4, c_84])).
% 1.93/1.19  tff(c_90, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_87])).
% 1.93/1.19  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_90])).
% 1.93/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  Inference rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Ref     : 0
% 1.93/1.19  #Sup     : 12
% 1.93/1.19  #Fact    : 0
% 1.93/1.19  #Define  : 0
% 1.93/1.19  #Split   : 0
% 1.93/1.19  #Chain   : 0
% 1.93/1.19  #Close   : 0
% 1.93/1.19  
% 1.93/1.19  Ordering : KBO
% 1.93/1.19  
% 1.93/1.19  Simplification rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Subsume      : 0
% 1.93/1.19  #Demod        : 13
% 1.93/1.19  #Tautology    : 6
% 1.93/1.19  #SimpNegUnit  : 5
% 1.93/1.19  #BackRed      : 0
% 1.93/1.19  
% 1.93/1.19  #Partial instantiations: 0
% 1.93/1.19  #Strategies tried      : 1
% 1.93/1.19  
% 1.93/1.19  Timing (in seconds)
% 1.93/1.19  ----------------------
% 1.93/1.19  Preprocessing        : 0.29
% 1.93/1.19  Parsing              : 0.17
% 1.93/1.19  CNF conversion       : 0.02
% 1.93/1.19  Main loop            : 0.12
% 1.93/1.19  Inferencing          : 0.06
% 1.93/1.19  Reduction            : 0.03
% 1.93/1.19  Demodulation         : 0.02
% 1.93/1.19  BG Simplification    : 0.01
% 1.93/1.19  Subsumption          : 0.02
% 1.93/1.19  Abstraction          : 0.01
% 1.93/1.19  MUC search           : 0.00
% 1.93/1.19  Cooper               : 0.00
% 1.93/1.19  Total                : 0.44
% 1.93/1.19  Index Insertion      : 0.00
% 1.93/1.19  Index Deletion       : 0.00
% 1.93/1.19  Index Matching       : 0.00
% 1.93/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
