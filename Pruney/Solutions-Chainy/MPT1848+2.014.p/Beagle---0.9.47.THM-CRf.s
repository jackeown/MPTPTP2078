%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:55 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_30,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    v1_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( m1_subset_1(u1_struct_0(B_5),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [B_24,A_25] :
      ( v1_subset_1(u1_struct_0(B_24),u1_struct_0(A_25))
      | ~ v1_tex_2(B_24,A_25)
      | ~ m1_subset_1(u1_struct_0(B_24),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_pre_topc(B_24,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_92,plain,(
    ! [B_26,A_27] :
      ( v1_subset_1(u1_struct_0(B_26),u1_struct_0(A_27))
      | ~ v1_tex_2(B_26,A_27)
      | ~ m1_pre_topc(B_26,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_114,plain,(
    ! [A_29] :
      ( v1_subset_1(u1_struct_0('#skF_1'),u1_struct_0(A_29))
      | ~ v1_tex_2('#skF_2',A_29)
      | ~ m1_pre_topc('#skF_2',A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_92])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : ~ v1_subset_1(k2_subset_1(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_19,plain,(
    ! [A_2] : ~ v1_subset_1(A_2,A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_124,plain,
    ( ~ v1_tex_2('#skF_2','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_19])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_12,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:57:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.22  
% 2.00/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.22  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.01/1.22  
% 2.01/1.22  %Foreground sorts:
% 2.01/1.22  
% 2.01/1.22  
% 2.01/1.22  %Background operators:
% 2.01/1.22  
% 2.01/1.22  
% 2.01/1.22  %Foreground operators:
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.22  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.01/1.22  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.01/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.01/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.01/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.01/1.22  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.01/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.22  
% 2.01/1.23  tff(f_62, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tex_2)).
% 2.01/1.23  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.01/1.23  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_tex_2)).
% 2.01/1.23  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.01/1.23  tff(f_30, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.01/1.23  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.01/1.23  tff(c_16, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.01/1.23  tff(c_12, plain, (v1_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.01/1.23  tff(c_14, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.01/1.23  tff(c_6, plain, (![B_5, A_3]: (m1_subset_1(u1_struct_0(B_5), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.01/1.23  tff(c_75, plain, (![B_24, A_25]: (v1_subset_1(u1_struct_0(B_24), u1_struct_0(A_25)) | ~v1_tex_2(B_24, A_25) | ~m1_subset_1(u1_struct_0(B_24), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_pre_topc(B_24, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.01/1.23  tff(c_92, plain, (![B_26, A_27]: (v1_subset_1(u1_struct_0(B_26), u1_struct_0(A_27)) | ~v1_tex_2(B_26, A_27) | ~m1_pre_topc(B_26, A_27) | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_6, c_75])).
% 2.01/1.23  tff(c_114, plain, (![A_29]: (v1_subset_1(u1_struct_0('#skF_1'), u1_struct_0(A_29)) | ~v1_tex_2('#skF_2', A_29) | ~m1_pre_topc('#skF_2', A_29) | ~l1_pre_topc(A_29))), inference(superposition, [status(thm), theory('equality')], [c_14, c_92])).
% 2.01/1.23  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.01/1.23  tff(c_4, plain, (![A_2]: (~v1_subset_1(k2_subset_1(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.01/1.23  tff(c_19, plain, (![A_2]: (~v1_subset_1(A_2, A_2))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.01/1.23  tff(c_124, plain, (~v1_tex_2('#skF_2', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_114, c_19])).
% 2.01/1.23  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_12, c_124])).
% 2.01/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.23  
% 2.01/1.23  Inference rules
% 2.01/1.23  ----------------------
% 2.01/1.23  #Ref     : 0
% 2.01/1.23  #Sup     : 27
% 2.01/1.23  #Fact    : 0
% 2.01/1.23  #Define  : 0
% 2.01/1.23  #Split   : 2
% 2.01/1.23  #Chain   : 0
% 2.01/1.23  #Close   : 0
% 2.01/1.23  
% 2.01/1.23  Ordering : KBO
% 2.01/1.23  
% 2.01/1.23  Simplification rules
% 2.01/1.23  ----------------------
% 2.01/1.23  #Subsume      : 8
% 2.01/1.23  #Demod        : 8
% 2.01/1.23  #Tautology    : 6
% 2.01/1.23  #SimpNegUnit  : 0
% 2.01/1.23  #BackRed      : 0
% 2.01/1.23  
% 2.01/1.23  #Partial instantiations: 0
% 2.01/1.23  #Strategies tried      : 1
% 2.01/1.23  
% 2.01/1.23  Timing (in seconds)
% 2.01/1.23  ----------------------
% 2.01/1.23  Preprocessing        : 0.31
% 2.01/1.23  Parsing              : 0.17
% 2.01/1.24  CNF conversion       : 0.02
% 2.01/1.24  Main loop            : 0.15
% 2.01/1.24  Inferencing          : 0.05
% 2.01/1.24  Reduction            : 0.04
% 2.01/1.24  Demodulation         : 0.03
% 2.01/1.24  BG Simplification    : 0.01
% 2.01/1.24  Subsumption          : 0.04
% 2.01/1.24  Abstraction          : 0.01
% 2.01/1.24  MUC search           : 0.00
% 2.01/1.24  Cooper               : 0.00
% 2.01/1.24  Total                : 0.48
% 2.01/1.24  Index Insertion      : 0.00
% 2.01/1.24  Index Deletion       : 0.00
% 2.01/1.24  Index Matching       : 0.00
% 2.01/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
