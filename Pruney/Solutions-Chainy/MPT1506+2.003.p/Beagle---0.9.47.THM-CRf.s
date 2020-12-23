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
% DateTime   : Thu Dec  3 10:24:46 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 ( 106 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r3_lattice3 > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(f_82,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

tff(f_33,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] : k16_lattice3(A,B) = k15_lattice3(A,a_2_1_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( B = k16_lattice3(A,C)
            <=> ( r3_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r3_lattice3(A,D,C)
                     => r3_lattices(A,D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    v4_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    r3_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [A_34,B_35] :
      ( k15_lattice3(A_34,a_2_1_lattice3(A_34,B_35)) = k16_lattice3(A_34,B_35)
      | ~ l3_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k15_lattice3(A_4,B_5),u1_struct_0(A_4))
      | ~ l3_lattices(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k16_lattice3(A_34,B_35),u1_struct_0(A_34))
      | ~ l3_lattices(A_34)
      | v2_struct_0(A_34)
      | ~ l3_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4])).

tff(c_51,plain,(
    ! [A_51,D_52,C_53] :
      ( r3_lattices(A_51,D_52,k16_lattice3(A_51,C_53))
      | ~ r3_lattice3(A_51,D_52,C_53)
      | ~ m1_subset_1(D_52,u1_struct_0(A_51))
      | ~ m1_subset_1(k16_lattice3(A_51,C_53),u1_struct_0(A_51))
      | ~ l3_lattices(A_51)
      | ~ v4_lattice3(A_51)
      | ~ v10_lattices(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_55,plain,(
    ! [A_54,D_55,B_56] :
      ( r3_lattices(A_54,D_55,k16_lattice3(A_54,B_56))
      | ~ r3_lattice3(A_54,D_55,B_56)
      | ~ m1_subset_1(D_55,u1_struct_0(A_54))
      | ~ v4_lattice3(A_54)
      | ~ v10_lattices(A_54)
      | ~ l3_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_16,plain,(
    ~ r3_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_62,plain,
    ( ~ r3_lattice3('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v4_lattice3('#skF_2')
    | ~ v10_lattices('#skF_2')
    | ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_16])).

tff(c_66,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_24,c_20,c_18,c_62])).

tff(c_68,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.15  
% 1.71/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.15  %$ r3_lattices > r3_lattice3 > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.71/1.15  
% 1.71/1.15  %Foreground sorts:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Background operators:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Foreground operators:
% 1.71/1.15  tff(l3_lattices, type, l3_lattices: $i > $o).
% 1.71/1.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.71/1.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.71/1.15  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.15  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 1.71/1.15  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 1.71/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.15  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 1.71/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.15  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 1.71/1.15  tff(v10_lattices, type, v10_lattices: $i > $o).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.71/1.15  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 1.71/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.71/1.15  
% 1.71/1.16  tff(f_82, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattice3)).
% 1.71/1.16  tff(f_33, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (k16_lattice3(A, B) = k15_lattice3(A, a_2_1_lattice3(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d22_lattice3)).
% 1.71/1.16  tff(f_40, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 1.71/1.16  tff(f_64, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 1.71/1.16  tff(c_28, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.71/1.16  tff(c_22, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.71/1.16  tff(c_26, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.71/1.16  tff(c_24, plain, (v4_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.71/1.16  tff(c_20, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.71/1.16  tff(c_18, plain, (r3_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.71/1.16  tff(c_30, plain, (![A_34, B_35]: (k15_lattice3(A_34, a_2_1_lattice3(A_34, B_35))=k16_lattice3(A_34, B_35) | ~l3_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.16  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k15_lattice3(A_4, B_5), u1_struct_0(A_4)) | ~l3_lattices(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.71/1.16  tff(c_36, plain, (![A_34, B_35]: (m1_subset_1(k16_lattice3(A_34, B_35), u1_struct_0(A_34)) | ~l3_lattices(A_34) | v2_struct_0(A_34) | ~l3_lattices(A_34) | v2_struct_0(A_34))), inference(superposition, [status(thm), theory('equality')], [c_30, c_4])).
% 1.71/1.16  tff(c_51, plain, (![A_51, D_52, C_53]: (r3_lattices(A_51, D_52, k16_lattice3(A_51, C_53)) | ~r3_lattice3(A_51, D_52, C_53) | ~m1_subset_1(D_52, u1_struct_0(A_51)) | ~m1_subset_1(k16_lattice3(A_51, C_53), u1_struct_0(A_51)) | ~l3_lattices(A_51) | ~v4_lattice3(A_51) | ~v10_lattices(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.71/1.16  tff(c_55, plain, (![A_54, D_55, B_56]: (r3_lattices(A_54, D_55, k16_lattice3(A_54, B_56)) | ~r3_lattice3(A_54, D_55, B_56) | ~m1_subset_1(D_55, u1_struct_0(A_54)) | ~v4_lattice3(A_54) | ~v10_lattices(A_54) | ~l3_lattices(A_54) | v2_struct_0(A_54))), inference(resolution, [status(thm)], [c_36, c_51])).
% 1.71/1.16  tff(c_16, plain, (~r3_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.71/1.16  tff(c_62, plain, (~r3_lattice3('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v4_lattice3('#skF_2') | ~v10_lattices('#skF_2') | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_55, c_16])).
% 1.71/1.16  tff(c_66, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26, c_24, c_20, c_18, c_62])).
% 1.71/1.16  tff(c_68, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_66])).
% 1.71/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  Inference rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Ref     : 0
% 1.71/1.16  #Sup     : 7
% 1.71/1.16  #Fact    : 0
% 1.71/1.16  #Define  : 0
% 1.71/1.16  #Split   : 0
% 1.71/1.16  #Chain   : 0
% 1.71/1.16  #Close   : 0
% 1.71/1.16  
% 1.71/1.16  Ordering : KBO
% 1.71/1.16  
% 1.71/1.16  Simplification rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Subsume      : 2
% 1.71/1.16  #Demod        : 5
% 1.71/1.16  #Tautology    : 2
% 1.71/1.16  #SimpNegUnit  : 1
% 1.71/1.16  #BackRed      : 0
% 1.71/1.16  
% 1.71/1.16  #Partial instantiations: 0
% 1.71/1.16  #Strategies tried      : 1
% 1.71/1.16  
% 1.71/1.16  Timing (in seconds)
% 1.71/1.16  ----------------------
% 1.71/1.17  Preprocessing        : 0.28
% 1.71/1.17  Parsing              : 0.16
% 1.71/1.17  CNF conversion       : 0.02
% 1.71/1.17  Main loop            : 0.13
% 1.71/1.17  Inferencing          : 0.06
% 1.71/1.17  Reduction            : 0.03
% 1.71/1.17  Demodulation         : 0.02
% 1.71/1.17  BG Simplification    : 0.01
% 1.71/1.17  Subsumption          : 0.02
% 1.71/1.17  Abstraction          : 0.01
% 1.71/1.17  MUC search           : 0.00
% 1.71/1.17  Cooper               : 0.00
% 1.71/1.17  Total                : 0.43
% 1.71/1.17  Index Insertion      : 0.00
% 1.71/1.17  Index Deletion       : 0.00
% 1.71/1.17  Index Matching       : 0.00
% 1.71/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
