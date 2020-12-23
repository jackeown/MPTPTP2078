%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:55 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  60 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_32,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] : ~ v1_subset_1(k2_subset_1(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_3] : ~ v1_subset_1(A_3,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_55,plain,(
    ! [B_26,A_27] :
      ( v1_subset_1(u1_struct_0(B_26),u1_struct_0(A_27))
      | ~ m1_subset_1(u1_struct_0(B_26),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ v1_tex_2(B_26,A_27)
      | ~ m1_pre_topc(B_26,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    ! [B_26] :
      ( v1_subset_1(u1_struct_0(B_26),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(u1_struct_0(B_26),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_tex_2(B_26,'#skF_2')
      | ~ m1_pre_topc(B_26,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_55])).

tff(c_79,plain,(
    ! [B_30] :
      ( v1_subset_1(u1_struct_0(B_30),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_30),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_tex_2(B_30,'#skF_2')
      | ~ m1_pre_topc(B_30,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_61])).

tff(c_86,plain,
    ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_23,c_79])).

tff(c_92,plain,(
    v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_86])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.18  
% 1.64/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.18  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.18  
% 1.89/1.18  %Foreground sorts:
% 1.89/1.18  
% 1.89/1.18  
% 1.89/1.18  %Background operators:
% 1.89/1.18  
% 1.89/1.18  
% 1.89/1.18  %Foreground operators:
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.18  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.89/1.18  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 1.89/1.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.89/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.18  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.89/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.89/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.18  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.89/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.18  
% 1.89/1.19  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.89/1.19  tff(f_32, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 1.89/1.19  tff(f_57, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 1.89/1.19  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.89/1.19  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 1.89/1.19  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.19  tff(c_6, plain, (![A_3]: (~v1_subset_1(k2_subset_1(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.19  tff(c_24, plain, (![A_3]: (~v1_subset_1(A_3, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.89/1.19  tff(c_20, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.19  tff(c_16, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.19  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.19  tff(c_23, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.89/1.19  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.19  tff(c_18, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.19  tff(c_55, plain, (![B_26, A_27]: (v1_subset_1(u1_struct_0(B_26), u1_struct_0(A_27)) | ~m1_subset_1(u1_struct_0(B_26), k1_zfmisc_1(u1_struct_0(A_27))) | ~v1_tex_2(B_26, A_27) | ~m1_pre_topc(B_26, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.89/1.19  tff(c_61, plain, (![B_26]: (v1_subset_1(u1_struct_0(B_26), u1_struct_0('#skF_2')) | ~m1_subset_1(u1_struct_0(B_26), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_tex_2(B_26, '#skF_2') | ~m1_pre_topc(B_26, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_55])).
% 1.89/1.19  tff(c_79, plain, (![B_30]: (v1_subset_1(u1_struct_0(B_30), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_30), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_tex_2(B_30, '#skF_2') | ~m1_pre_topc(B_30, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_61])).
% 1.89/1.19  tff(c_86, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_23, c_79])).
% 1.89/1.19  tff(c_92, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_86])).
% 1.89/1.19  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_92])).
% 1.89/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  Inference rules
% 1.89/1.19  ----------------------
% 1.89/1.19  #Ref     : 0
% 1.89/1.19  #Sup     : 12
% 1.89/1.19  #Fact    : 0
% 1.89/1.19  #Define  : 0
% 1.89/1.19  #Split   : 0
% 1.89/1.19  #Chain   : 0
% 1.89/1.19  #Close   : 0
% 1.89/1.19  
% 1.89/1.19  Ordering : KBO
% 1.89/1.19  
% 1.89/1.19  Simplification rules
% 1.89/1.19  ----------------------
% 1.89/1.19  #Subsume      : 0
% 1.89/1.19  #Demod        : 11
% 1.89/1.19  #Tautology    : 4
% 1.89/1.19  #SimpNegUnit  : 3
% 1.89/1.19  #BackRed      : 0
% 1.89/1.19  
% 1.89/1.19  #Partial instantiations: 0
% 1.89/1.19  #Strategies tried      : 1
% 1.89/1.19  
% 1.89/1.19  Timing (in seconds)
% 1.89/1.19  ----------------------
% 1.89/1.20  Preprocessing        : 0.31
% 1.89/1.20  Parsing              : 0.16
% 1.89/1.20  CNF conversion       : 0.02
% 1.89/1.20  Main loop            : 0.11
% 1.89/1.20  Inferencing          : 0.04
% 1.89/1.20  Reduction            : 0.04
% 1.89/1.20  Demodulation         : 0.03
% 1.89/1.20  BG Simplification    : 0.01
% 1.89/1.20  Subsumption          : 0.02
% 1.89/1.20  Abstraction          : 0.01
% 1.89/1.20  MUC search           : 0.00
% 1.89/1.20  Cooper               : 0.00
% 1.89/1.20  Total                : 0.44
% 1.89/1.20  Index Insertion      : 0.00
% 1.89/1.20  Index Deletion       : 0.00
% 1.89/1.20  Index Matching       : 0.00
% 1.89/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
