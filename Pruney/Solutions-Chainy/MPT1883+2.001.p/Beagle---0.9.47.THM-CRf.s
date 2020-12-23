%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:19 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   42 (  76 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 236 expanded)
%              Number of equality atoms :    7 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => ( v3_tex_2(C,A)
                  <=> v4_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,
    ( ~ v4_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_31,plain,(
    ~ v3_tex_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_16,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,
    ( v3_tex_2('#skF_4','#skF_2')
    | v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_26])).

tff(c_12,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [B_21,A_22] :
      ( v3_tex_2(u1_struct_0(B_21),A_22)
      | ~ m1_subset_1(u1_struct_0(B_21),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v4_tex_2(B_21,A_22)
      | ~ m1_pre_topc(B_21,A_22)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    ! [A_22] :
      ( v3_tex_2(u1_struct_0('#skF_3'),A_22)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v4_tex_2('#skF_3',A_22)
      | ~ m1_pre_topc('#skF_3',A_22)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_48,plain,(
    ! [A_23] :
      ( v3_tex_2('#skF_4',A_23)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ v4_tex_2('#skF_3',A_23)
      | ~ m1_pre_topc('#skF_3',A_23)
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_43])).

tff(c_51,plain,
    ( v3_tex_2('#skF_4','#skF_2')
    | ~ v4_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_48])).

tff(c_57,plain,
    ( v3_tex_2('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_32,c_51])).

tff(c_59,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_31,c_57])).

tff(c_60,plain,(
    ~ v4_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_61,plain,(
    v3_tex_2('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_65,plain,(
    ! [B_26,A_27] :
      ( u1_struct_0(B_26) = '#skF_1'(A_27,B_26)
      | v4_tex_2(B_26,A_27)
      | ~ m1_pre_topc(B_26,A_27)
      | ~ l1_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_60])).

tff(c_71,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_10,c_68])).

tff(c_72,plain,(
    '#skF_1'('#skF_2','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_71])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v3_tex_2('#skF_1'(A_1,B_7),A_1)
      | v4_tex_2(B_7,A_1)
      | ~ m1_pre_topc(B_7,A_1)
      | ~ l1_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,
    ( ~ v3_tex_2('#skF_4','#skF_2')
    | v4_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4])).

tff(c_80,plain,
    ( v4_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_61,c_76])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_60,c_80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.13  
% 1.78/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.13  %$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.78/1.13  
% 1.78/1.13  %Foreground sorts:
% 1.78/1.13  
% 1.78/1.13  
% 1.78/1.13  %Background operators:
% 1.78/1.13  
% 1.78/1.13  
% 1.78/1.13  %Foreground operators:
% 1.78/1.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.78/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.13  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 1.78/1.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.78/1.13  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 1.78/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.78/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.13  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.78/1.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.78/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.78/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.78/1.13  
% 1.78/1.14  tff(f_60, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v3_tex_2(C, A) <=> v4_tex_2(B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_tex_2)).
% 1.78/1.14  tff(f_42, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 1.78/1.14  tff(c_18, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.78/1.14  tff(c_20, plain, (~v4_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.78/1.14  tff(c_31, plain, (~v3_tex_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 1.78/1.14  tff(c_16, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.78/1.14  tff(c_14, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.78/1.14  tff(c_26, plain, (v3_tex_2('#skF_4', '#skF_2') | v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.78/1.14  tff(c_32, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_31, c_26])).
% 1.78/1.14  tff(c_12, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.78/1.14  tff(c_10, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.78/1.14  tff(c_40, plain, (![B_21, A_22]: (v3_tex_2(u1_struct_0(B_21), A_22) | ~m1_subset_1(u1_struct_0(B_21), k1_zfmisc_1(u1_struct_0(A_22))) | ~v4_tex_2(B_21, A_22) | ~m1_pre_topc(B_21, A_22) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.78/1.14  tff(c_43, plain, (![A_22]: (v3_tex_2(u1_struct_0('#skF_3'), A_22) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_22))) | ~v4_tex_2('#skF_3', A_22) | ~m1_pre_topc('#skF_3', A_22) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(superposition, [status(thm), theory('equality')], [c_10, c_40])).
% 1.78/1.14  tff(c_48, plain, (![A_23]: (v3_tex_2('#skF_4', A_23) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_23))) | ~v4_tex_2('#skF_3', A_23) | ~m1_pre_topc('#skF_3', A_23) | ~l1_pre_topc(A_23) | v2_struct_0(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_43])).
% 1.78/1.14  tff(c_51, plain, (v3_tex_2('#skF_4', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_48])).
% 1.78/1.14  tff(c_57, plain, (v3_tex_2('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_32, c_51])).
% 1.78/1.14  tff(c_59, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_31, c_57])).
% 1.78/1.14  tff(c_60, plain, (~v4_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_20])).
% 1.78/1.14  tff(c_61, plain, (v3_tex_2('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_20])).
% 1.78/1.14  tff(c_65, plain, (![B_26, A_27]: (u1_struct_0(B_26)='#skF_1'(A_27, B_26) | v4_tex_2(B_26, A_27) | ~m1_pre_topc(B_26, A_27) | ~l1_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.78/1.14  tff(c_68, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_65, c_60])).
% 1.78/1.14  tff(c_71, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_10, c_68])).
% 1.78/1.14  tff(c_72, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_18, c_71])).
% 1.78/1.14  tff(c_4, plain, (![A_1, B_7]: (~v3_tex_2('#skF_1'(A_1, B_7), A_1) | v4_tex_2(B_7, A_1) | ~m1_pre_topc(B_7, A_1) | ~l1_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.78/1.14  tff(c_76, plain, (~v3_tex_2('#skF_4', '#skF_2') | v4_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72, c_4])).
% 1.78/1.14  tff(c_80, plain, (v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_61, c_76])).
% 1.78/1.14  tff(c_82, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_60, c_80])).
% 1.78/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.14  
% 1.78/1.14  Inference rules
% 1.78/1.14  ----------------------
% 1.78/1.14  #Ref     : 0
% 1.78/1.14  #Sup     : 11
% 1.78/1.14  #Fact    : 0
% 1.78/1.14  #Define  : 0
% 1.78/1.14  #Split   : 2
% 1.78/1.14  #Chain   : 0
% 1.78/1.14  #Close   : 0
% 1.78/1.14  
% 1.78/1.14  Ordering : KBO
% 1.78/1.14  
% 1.78/1.14  Simplification rules
% 1.78/1.14  ----------------------
% 1.78/1.14  #Subsume      : 1
% 1.78/1.14  #Demod        : 11
% 1.78/1.14  #Tautology    : 6
% 1.78/1.14  #SimpNegUnit  : 5
% 1.78/1.14  #BackRed      : 0
% 1.78/1.14  
% 1.78/1.14  #Partial instantiations: 0
% 1.78/1.14  #Strategies tried      : 1
% 1.78/1.14  
% 1.78/1.14  Timing (in seconds)
% 1.78/1.14  ----------------------
% 1.84/1.15  Preprocessing        : 0.28
% 1.84/1.15  Parsing              : 0.14
% 1.84/1.15  CNF conversion       : 0.02
% 1.84/1.15  Main loop            : 0.11
% 1.84/1.15  Inferencing          : 0.04
% 1.84/1.15  Reduction            : 0.03
% 1.84/1.15  Demodulation         : 0.02
% 1.84/1.15  BG Simplification    : 0.01
% 1.84/1.15  Subsumption          : 0.01
% 1.84/1.15  Abstraction          : 0.01
% 1.84/1.15  MUC search           : 0.00
% 1.84/1.15  Cooper               : 0.00
% 1.84/1.15  Total                : 0.41
% 1.84/1.15  Index Insertion      : 0.00
% 1.84/1.15  Index Deletion       : 0.00
% 1.84/1.15  Index Matching       : 0.00
% 1.84/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
