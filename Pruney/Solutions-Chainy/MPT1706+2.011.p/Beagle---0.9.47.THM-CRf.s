%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:26 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   53 ( 119 expanded)
%              Number of equality atoms :    1 (   7 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
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
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ? [E] :
                          ( m1_subset_1(E,u1_struct_0(C))
                          & E = D ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tmap_1)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(c_14,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_25,plain,(
    ! [B_38,A_39] :
      ( l1_pre_topc(B_38)
      | ~ m1_pre_topc(B_38,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_31,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_25])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_31])).

tff(c_10,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,(
    ! [C_40,A_41,B_42] :
      ( m1_subset_1(C_40,u1_struct_0(A_41))
      | ~ m1_subset_1(C_40,u1_struct_0(B_42))
      | ~ m1_pre_topc(B_42,A_41)
      | v2_struct_0(B_42)
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    ! [A_41] :
      ( m1_subset_1('#skF_4',u1_struct_0(A_41))
      | ~ m1_pre_topc('#skF_2',A_41)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_50,plain,(
    ! [A_43] :
      ( m1_subset_1('#skF_4',u1_struct_0(A_43))
      | ~ m1_pre_topc('#skF_2',A_43)
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_46])).

tff(c_6,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_6])).

tff(c_59,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10,c_55])).

tff(c_61,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:27:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.19  
% 1.82/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.19  %$ m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.82/1.19  
% 1.82/1.19  %Foreground sorts:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Background operators:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Foreground operators:
% 1.82/1.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.82/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.19  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.82/1.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.82/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.82/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.19  
% 1.82/1.20  tff(f_78, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tmap_1)).
% 1.82/1.20  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 1.82/1.20  tff(f_48, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 1.82/1.20  tff(c_14, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.82/1.20  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.82/1.20  tff(c_12, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.82/1.20  tff(c_25, plain, (![B_38, A_39]: (l1_pre_topc(B_38) | ~m1_pre_topc(B_38, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.20  tff(c_31, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_25])).
% 1.82/1.20  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_31])).
% 1.82/1.20  tff(c_10, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.82/1.20  tff(c_18, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.82/1.20  tff(c_8, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.82/1.20  tff(c_44, plain, (![C_40, A_41, B_42]: (m1_subset_1(C_40, u1_struct_0(A_41)) | ~m1_subset_1(C_40, u1_struct_0(B_42)) | ~m1_pre_topc(B_42, A_41) | v2_struct_0(B_42) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.82/1.20  tff(c_46, plain, (![A_41]: (m1_subset_1('#skF_4', u1_struct_0(A_41)) | ~m1_pre_topc('#skF_2', A_41) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_8, c_44])).
% 1.82/1.20  tff(c_50, plain, (![A_43]: (m1_subset_1('#skF_4', u1_struct_0(A_43)) | ~m1_pre_topc('#skF_2', A_43) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(negUnitSimplification, [status(thm)], [c_18, c_46])).
% 1.82/1.20  tff(c_6, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.82/1.20  tff(c_55, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_6])).
% 1.82/1.20  tff(c_59, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10, c_55])).
% 1.82/1.20  tff(c_61, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_59])).
% 1.82/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.20  
% 1.82/1.20  Inference rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Ref     : 0
% 1.82/1.20  #Sup     : 6
% 1.82/1.20  #Fact    : 0
% 1.82/1.20  #Define  : 0
% 1.82/1.20  #Split   : 0
% 1.82/1.20  #Chain   : 0
% 1.82/1.20  #Close   : 0
% 1.82/1.20  
% 1.82/1.20  Ordering : KBO
% 1.82/1.20  
% 1.82/1.20  Simplification rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Subsume      : 0
% 1.82/1.20  #Demod        : 6
% 1.82/1.20  #Tautology    : 1
% 1.82/1.20  #SimpNegUnit  : 2
% 1.82/1.20  #BackRed      : 0
% 1.82/1.20  
% 1.82/1.20  #Partial instantiations: 0
% 1.82/1.20  #Strategies tried      : 1
% 1.82/1.20  
% 1.82/1.20  Timing (in seconds)
% 1.82/1.20  ----------------------
% 1.82/1.21  Preprocessing        : 0.30
% 1.82/1.21  Parsing              : 0.16
% 1.82/1.21  CNF conversion       : 0.02
% 1.82/1.21  Main loop            : 0.11
% 1.82/1.21  Inferencing          : 0.04
% 1.82/1.21  Reduction            : 0.03
% 1.82/1.21  Demodulation         : 0.02
% 1.82/1.21  BG Simplification    : 0.01
% 1.82/1.21  Subsumption          : 0.02
% 1.82/1.21  Abstraction          : 0.00
% 1.82/1.21  MUC search           : 0.00
% 1.82/1.21  Cooper               : 0.00
% 1.82/1.21  Total                : 0.43
% 1.82/1.21  Index Insertion      : 0.00
% 1.82/1.21  Index Deletion       : 0.00
% 1.89/1.21  Index Matching       : 0.00
% 1.89/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
