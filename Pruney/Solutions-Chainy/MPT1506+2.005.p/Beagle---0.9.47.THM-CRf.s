%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:46 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   53 (  95 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r3_lattice3 > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_74,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_56,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    v4_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    r3_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k16_lattice3(A_1,B_2),u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [A_44,D_45,C_46] :
      ( r3_lattices(A_44,D_45,k16_lattice3(A_44,C_46))
      | ~ r3_lattice3(A_44,D_45,C_46)
      | ~ m1_subset_1(D_45,u1_struct_0(A_44))
      | ~ m1_subset_1(k16_lattice3(A_44,C_46),u1_struct_0(A_44))
      | ~ l3_lattices(A_44)
      | ~ v4_lattice3(A_44)
      | ~ v10_lattices(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [A_47,D_48,B_49] :
      ( r3_lattices(A_47,D_48,k16_lattice3(A_47,B_49))
      | ~ r3_lattice3(A_47,D_48,B_49)
      | ~ m1_subset_1(D_48,u1_struct_0(A_47))
      | ~ v4_lattice3(A_47)
      | ~ v10_lattices(A_47)
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_2,c_36])).

tff(c_14,plain,(
    ~ r3_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_47,plain,
    ( ~ r3_lattice3('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v4_lattice3('#skF_2')
    | ~ v10_lattices('#skF_2')
    | ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_14])).

tff(c_51,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24,c_22,c_18,c_16,c_47])).

tff(c_53,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.17  
% 1.79/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.17  %$ r3_lattices > r3_lattice3 > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.79/1.17  
% 1.79/1.17  %Foreground sorts:
% 1.79/1.17  
% 1.79/1.17  
% 1.79/1.17  %Background operators:
% 1.79/1.17  
% 1.79/1.17  
% 1.79/1.17  %Foreground operators:
% 1.79/1.17  tff(l3_lattices, type, l3_lattices: $i > $o).
% 1.79/1.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.79/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.79/1.17  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.17  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 1.79/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.17  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 1.79/1.17  tff(v10_lattices, type, v10_lattices: $i > $o).
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.79/1.17  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 1.79/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.17  
% 1.79/1.18  tff(f_74, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattice3)).
% 1.79/1.18  tff(f_32, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 1.79/1.18  tff(f_56, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 1.79/1.18  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.79/1.18  tff(c_20, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.79/1.18  tff(c_24, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.79/1.18  tff(c_22, plain, (v4_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.79/1.18  tff(c_18, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.79/1.18  tff(c_16, plain, (r3_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.79/1.18  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k16_lattice3(A_1, B_2), u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.18  tff(c_36, plain, (![A_44, D_45, C_46]: (r3_lattices(A_44, D_45, k16_lattice3(A_44, C_46)) | ~r3_lattice3(A_44, D_45, C_46) | ~m1_subset_1(D_45, u1_struct_0(A_44)) | ~m1_subset_1(k16_lattice3(A_44, C_46), u1_struct_0(A_44)) | ~l3_lattices(A_44) | ~v4_lattice3(A_44) | ~v10_lattices(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.79/1.18  tff(c_40, plain, (![A_47, D_48, B_49]: (r3_lattices(A_47, D_48, k16_lattice3(A_47, B_49)) | ~r3_lattice3(A_47, D_48, B_49) | ~m1_subset_1(D_48, u1_struct_0(A_47)) | ~v4_lattice3(A_47) | ~v10_lattices(A_47) | ~l3_lattices(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_2, c_36])).
% 1.79/1.18  tff(c_14, plain, (~r3_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.79/1.18  tff(c_47, plain, (~r3_lattice3('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v4_lattice3('#skF_2') | ~v10_lattices('#skF_2') | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_14])).
% 1.79/1.18  tff(c_51, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24, c_22, c_18, c_16, c_47])).
% 1.79/1.18  tff(c_53, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_51])).
% 1.79/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  Inference rules
% 1.79/1.18  ----------------------
% 1.79/1.18  #Ref     : 0
% 1.79/1.18  #Sup     : 4
% 1.79/1.18  #Fact    : 0
% 1.79/1.18  #Define  : 0
% 1.79/1.18  #Split   : 0
% 1.79/1.18  #Chain   : 0
% 1.79/1.18  #Close   : 0
% 1.79/1.18  
% 1.79/1.18  Ordering : KBO
% 1.79/1.18  
% 1.79/1.18  Simplification rules
% 1.79/1.18  ----------------------
% 1.79/1.18  #Subsume      : 2
% 1.79/1.18  #Demod        : 5
% 1.79/1.18  #Tautology    : 0
% 1.79/1.18  #SimpNegUnit  : 1
% 1.79/1.18  #BackRed      : 0
% 1.79/1.18  
% 1.79/1.18  #Partial instantiations: 0
% 1.79/1.18  #Strategies tried      : 1
% 1.79/1.18  
% 1.79/1.18  Timing (in seconds)
% 1.79/1.18  ----------------------
% 1.79/1.18  Preprocessing        : 0.27
% 1.79/1.18  Parsing              : 0.14
% 1.79/1.18  CNF conversion       : 0.02
% 1.79/1.18  Main loop            : 0.12
% 1.79/1.18  Inferencing          : 0.05
% 1.79/1.18  Reduction            : 0.03
% 1.79/1.18  Demodulation         : 0.02
% 1.79/1.18  BG Simplification    : 0.01
% 1.79/1.18  Subsumption          : 0.02
% 1.79/1.18  Abstraction          : 0.01
% 1.79/1.18  MUC search           : 0.00
% 1.79/1.18  Cooper               : 0.00
% 1.79/1.18  Total                : 0.41
% 1.79/1.18  Index Insertion      : 0.00
% 1.79/1.18  Index Deletion       : 0.00
% 1.79/1.18  Index Matching       : 0.00
% 1.79/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
