%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:55 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  74 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_30,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_36,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : ~ v1_subset_1(k2_subset_1(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_29,plain,(
    ! [A_2] : ~ v1_subset_1(A_2,A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_26,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    v1_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_3] : ~ v1_subset_1('#skF_1'(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1('#skF_1'(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,(
    ! [B_22,A_23] :
      ( v1_subset_1(B_22,A_23)
      | B_22 = A_23
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,(
    ! [A_3] :
      ( v1_subset_1('#skF_1'(A_3),A_3)
      | '#skF_1'(A_3) = A_3 ) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_52,plain,(
    ! [A_3] : '#skF_1'(A_3) = A_3 ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_49])).

tff(c_54,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_28,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_90,plain,(
    ! [B_33,A_34] :
      ( v1_subset_1(u1_struct_0(B_33),u1_struct_0(A_34))
      | ~ m1_subset_1(u1_struct_0(B_33),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ v1_tex_2(B_33,A_34)
      | ~ m1_pre_topc(B_33,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_100,plain,(
    ! [B_33] :
      ( v1_subset_1(u1_struct_0(B_33),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_33),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v1_tex_2(B_33,'#skF_3')
      | ~ m1_pre_topc(B_33,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_90])).

tff(c_119,plain,(
    ! [B_38] :
      ( v1_subset_1(u1_struct_0(B_38),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v1_tex_2(B_38,'#skF_3')
      | ~ m1_pre_topc(B_38,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_100])).

tff(c_123,plain,
    ( v1_subset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v1_tex_2('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_119])).

tff(c_129,plain,(
    v1_subset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_123])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:08:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.18  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.91/1.18  
% 1.91/1.18  %Foreground sorts:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Background operators:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Foreground operators:
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.18  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.91/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.91/1.18  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 1.91/1.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.91/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.18  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.91/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.91/1.18  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.91/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.18  
% 1.91/1.19  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.91/1.19  tff(f_30, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 1.91/1.19  tff(f_68, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tex_2)).
% 1.91/1.19  tff(f_36, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 1.91/1.19  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 1.91/1.19  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 1.91/1.19  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.19  tff(c_4, plain, (![A_2]: (~v1_subset_1(k2_subset_1(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.91/1.19  tff(c_29, plain, (![A_2]: (~v1_subset_1(A_2, A_2))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.91/1.19  tff(c_26, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.91/1.19  tff(c_22, plain, (v1_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.91/1.19  tff(c_6, plain, (![A_3]: (~v1_subset_1('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.91/1.19  tff(c_8, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.91/1.19  tff(c_46, plain, (![B_22, A_23]: (v1_subset_1(B_22, A_23) | B_22=A_23 | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.19  tff(c_49, plain, (![A_3]: (v1_subset_1('#skF_1'(A_3), A_3) | '#skF_1'(A_3)=A_3)), inference(resolution, [status(thm)], [c_8, c_46])).
% 1.91/1.19  tff(c_52, plain, (![A_3]: ('#skF_1'(A_3)=A_3)), inference(negUnitSimplification, [status(thm)], [c_6, c_49])).
% 1.91/1.19  tff(c_54, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8])).
% 1.91/1.19  tff(c_28, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.91/1.19  tff(c_24, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.91/1.19  tff(c_90, plain, (![B_33, A_34]: (v1_subset_1(u1_struct_0(B_33), u1_struct_0(A_34)) | ~m1_subset_1(u1_struct_0(B_33), k1_zfmisc_1(u1_struct_0(A_34))) | ~v1_tex_2(B_33, A_34) | ~m1_pre_topc(B_33, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.19  tff(c_100, plain, (![B_33]: (v1_subset_1(u1_struct_0(B_33), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_33), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v1_tex_2(B_33, '#skF_3') | ~m1_pre_topc(B_33, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_90])).
% 1.91/1.19  tff(c_119, plain, (![B_38]: (v1_subset_1(u1_struct_0(B_38), u1_struct_0('#skF_4')) | ~m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v1_tex_2(B_38, '#skF_3') | ~m1_pre_topc(B_38, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_100])).
% 1.91/1.19  tff(c_123, plain, (v1_subset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_4')) | ~v1_tex_2('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_119])).
% 1.91/1.19  tff(c_129, plain, (v1_subset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_123])).
% 1.91/1.19  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29, c_129])).
% 1.91/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  Inference rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Ref     : 0
% 1.91/1.20  #Sup     : 18
% 1.91/1.20  #Fact    : 0
% 1.91/1.20  #Define  : 0
% 1.91/1.20  #Split   : 0
% 1.91/1.20  #Chain   : 0
% 1.91/1.20  #Close   : 0
% 1.91/1.20  
% 1.91/1.20  Ordering : KBO
% 1.91/1.20  
% 1.91/1.20  Simplification rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Subsume      : 2
% 1.91/1.20  #Demod        : 10
% 1.91/1.20  #Tautology    : 7
% 1.91/1.20  #SimpNegUnit  : 4
% 1.91/1.20  #BackRed      : 2
% 1.91/1.20  
% 1.91/1.20  #Partial instantiations: 0
% 1.91/1.20  #Strategies tried      : 1
% 1.91/1.20  
% 1.91/1.20  Timing (in seconds)
% 1.91/1.20  ----------------------
% 1.91/1.20  Preprocessing        : 0.29
% 1.91/1.20  Parsing              : 0.15
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.14
% 1.91/1.20  Inferencing          : 0.05
% 1.91/1.20  Reduction            : 0.04
% 1.91/1.20  Demodulation         : 0.03
% 1.91/1.20  BG Simplification    : 0.01
% 1.91/1.20  Subsumption          : 0.03
% 1.91/1.20  Abstraction          : 0.01
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.45
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.20  Index Deletion       : 0.00
% 1.91/1.20  Index Matching       : 0.00
% 1.91/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
