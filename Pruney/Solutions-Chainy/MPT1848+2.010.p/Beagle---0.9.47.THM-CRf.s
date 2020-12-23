%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:55 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  56 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_51,axiom,(
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

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_30,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( m1_subset_1(u1_struct_0(B_5),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,(
    ! [B_31,A_32] :
      ( v1_subset_1(u1_struct_0(B_31),u1_struct_0(A_32))
      | ~ m1_subset_1(u1_struct_0(B_31),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ v1_tex_2(B_31,A_32)
      | ~ m1_pre_topc(B_31,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95,plain,(
    ! [B_33,A_34] :
      ( v1_subset_1(u1_struct_0(B_33),u1_struct_0(A_34))
      | ~ v1_tex_2(B_33,A_34)
      | ~ m1_pre_topc(B_33,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_105,plain,(
    ! [B_33] :
      ( v1_subset_1(u1_struct_0(B_33),u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_33,'#skF_2')
      | ~ m1_pre_topc(B_33,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_95])).

tff(c_129,plain,(
    ! [B_38] :
      ( v1_subset_1(u1_struct_0(B_38),u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_38,'#skF_2')
      | ~ m1_pre_topc(B_38,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_105])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : ~ v1_subset_1(k2_subset_1(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_23,plain,(
    ! [A_2] : ~ v1_subset_1(A_2,A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_133,plain,
    ( ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_129,c_23])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.21  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.21  
% 1.98/1.21  %Foreground sorts:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Background operators:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Foreground operators:
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.21  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.98/1.21  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 1.98/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.98/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.21  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.98/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.21  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.98/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.21  
% 1.98/1.22  tff(f_62, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 1.98/1.22  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 1.98/1.22  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 1.98/1.22  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.98/1.22  tff(f_30, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 1.98/1.22  tff(c_20, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.98/1.22  tff(c_16, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.98/1.22  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.98/1.22  tff(c_18, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.98/1.22  tff(c_6, plain, (![B_5, A_3]: (m1_subset_1(u1_struct_0(B_5), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.98/1.22  tff(c_73, plain, (![B_31, A_32]: (v1_subset_1(u1_struct_0(B_31), u1_struct_0(A_32)) | ~m1_subset_1(u1_struct_0(B_31), k1_zfmisc_1(u1_struct_0(A_32))) | ~v1_tex_2(B_31, A_32) | ~m1_pre_topc(B_31, A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.22  tff(c_95, plain, (![B_33, A_34]: (v1_subset_1(u1_struct_0(B_33), u1_struct_0(A_34)) | ~v1_tex_2(B_33, A_34) | ~m1_pre_topc(B_33, A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_6, c_73])).
% 1.98/1.22  tff(c_105, plain, (![B_33]: (v1_subset_1(u1_struct_0(B_33), u1_struct_0('#skF_3')) | ~v1_tex_2(B_33, '#skF_2') | ~m1_pre_topc(B_33, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_95])).
% 1.98/1.22  tff(c_129, plain, (![B_38]: (v1_subset_1(u1_struct_0(B_38), u1_struct_0('#skF_3')) | ~v1_tex_2(B_38, '#skF_2') | ~m1_pre_topc(B_38, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_105])).
% 1.98/1.22  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.22  tff(c_4, plain, (![A_2]: (~v1_subset_1(k2_subset_1(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.98/1.22  tff(c_23, plain, (![A_2]: (~v1_subset_1(A_2, A_2))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.98/1.22  tff(c_133, plain, (~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_129, c_23])).
% 1.98/1.22  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_133])).
% 1.98/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  Inference rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Ref     : 0
% 1.98/1.22  #Sup     : 23
% 1.98/1.22  #Fact    : 0
% 1.98/1.22  #Define  : 0
% 1.98/1.22  #Split   : 2
% 1.98/1.22  #Chain   : 0
% 1.98/1.22  #Close   : 0
% 1.98/1.22  
% 1.98/1.22  Ordering : KBO
% 1.98/1.22  
% 1.98/1.22  Simplification rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Subsume      : 3
% 1.98/1.22  #Demod        : 12
% 1.98/1.22  #Tautology    : 4
% 1.98/1.22  #SimpNegUnit  : 1
% 1.98/1.22  #BackRed      : 0
% 1.98/1.22  
% 1.98/1.22  #Partial instantiations: 0
% 1.98/1.22  #Strategies tried      : 1
% 1.98/1.22  
% 1.98/1.22  Timing (in seconds)
% 1.98/1.22  ----------------------
% 1.98/1.23  Preprocessing        : 0.28
% 1.98/1.23  Parsing              : 0.15
% 1.98/1.23  CNF conversion       : 0.02
% 1.98/1.23  Main loop            : 0.15
% 1.98/1.23  Inferencing          : 0.06
% 1.98/1.23  Reduction            : 0.04
% 1.98/1.23  Demodulation         : 0.03
% 1.98/1.23  BG Simplification    : 0.01
% 1.98/1.23  Subsumption          : 0.03
% 1.98/1.23  Abstraction          : 0.01
% 1.98/1.23  MUC search           : 0.00
% 1.98/1.23  Cooper               : 0.00
% 1.98/1.23  Total                : 0.46
% 1.98/1.23  Index Insertion      : 0.00
% 1.98/1.23  Index Deletion       : 0.00
% 1.98/1.23  Index Matching       : 0.00
% 1.98/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
