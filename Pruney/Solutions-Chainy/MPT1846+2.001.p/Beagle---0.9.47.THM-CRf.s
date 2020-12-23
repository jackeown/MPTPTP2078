%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:52 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   39 (  68 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 181 expanded)
%              Number of equality atoms :    6 (  25 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => ( v1_subset_1(C,u1_struct_0(A))
                  <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

tff(f_39,axiom,(
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

tff(c_18,plain,
    ( ~ v1_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_16,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_24])).

tff(c_12,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    ! [B_21,A_22] :
      ( v1_subset_1(u1_struct_0(B_21),u1_struct_0(A_22))
      | ~ m1_subset_1(u1_struct_0(B_21),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v1_tex_2(B_21,A_22)
      | ~ m1_pre_topc(B_21,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_22] :
      ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0(A_22))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v1_tex_2('#skF_3',A_22)
      | ~ m1_pre_topc('#skF_3',A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_41])).

tff(c_50,plain,(
    ! [A_23] :
      ( v1_subset_1('#skF_4',u1_struct_0(A_23))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ v1_tex_2('#skF_3',A_23)
      | ~ m1_pre_topc('#skF_3',A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_53,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_50])).

tff(c_59,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_30,c_53])).

tff(c_61,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_59])).

tff(c_62,plain,(
    ~ v1_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_63,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_66,plain,(
    ! [B_24,A_25] :
      ( u1_struct_0(B_24) = '#skF_1'(A_25,B_24)
      | v1_tex_2(B_24,A_25)
      | ~ m1_pre_topc(B_24,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_62])).

tff(c_72,plain,(
    '#skF_1'('#skF_2','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_10,c_69])).

tff(c_77,plain,(
    ! [A_26,B_27] :
      ( ~ v1_subset_1('#skF_1'(A_26,B_27),u1_struct_0(A_26))
      | v1_tex_2(B_27,A_26)
      | ~ m1_pre_topc(B_27,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,
    ( ~ v1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_77])).

tff(c_85,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_63,c_80])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:34:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.31  
% 1.76/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.31  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.76/1.31  
% 1.76/1.31  %Foreground sorts:
% 1.76/1.31  
% 1.76/1.31  
% 1.76/1.31  %Background operators:
% 1.76/1.31  
% 1.76/1.31  
% 1.76/1.31  %Foreground operators:
% 1.76/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.31  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.76/1.31  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 1.76/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.76/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.76/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.31  tff('#skF_4', type, '#skF_4': $i).
% 1.76/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.31  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.76/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.76/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.76/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.76/1.31  
% 1.76/1.32  tff(f_54, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 1.76/1.32  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 1.76/1.32  tff(c_18, plain, (~v1_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.76/1.32  tff(c_29, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_18])).
% 1.76/1.32  tff(c_16, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.76/1.32  tff(c_14, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.76/1.32  tff(c_24, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.76/1.32  tff(c_30, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_29, c_24])).
% 1.76/1.32  tff(c_12, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.76/1.32  tff(c_10, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.76/1.32  tff(c_41, plain, (![B_21, A_22]: (v1_subset_1(u1_struct_0(B_21), u1_struct_0(A_22)) | ~m1_subset_1(u1_struct_0(B_21), k1_zfmisc_1(u1_struct_0(A_22))) | ~v1_tex_2(B_21, A_22) | ~m1_pre_topc(B_21, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.76/1.32  tff(c_44, plain, (![A_22]: (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0(A_22)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_22))) | ~v1_tex_2('#skF_3', A_22) | ~m1_pre_topc('#skF_3', A_22) | ~l1_pre_topc(A_22))), inference(superposition, [status(thm), theory('equality')], [c_10, c_41])).
% 1.76/1.32  tff(c_50, plain, (![A_23]: (v1_subset_1('#skF_4', u1_struct_0(A_23)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_23))) | ~v1_tex_2('#skF_3', A_23) | ~m1_pre_topc('#skF_3', A_23) | ~l1_pre_topc(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_44])).
% 1.76/1.32  tff(c_53, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_50])).
% 1.76/1.32  tff(c_59, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_30, c_53])).
% 1.76/1.32  tff(c_61, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29, c_59])).
% 1.76/1.32  tff(c_62, plain, (~v1_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 1.76/1.32  tff(c_63, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_18])).
% 1.76/1.32  tff(c_66, plain, (![B_24, A_25]: (u1_struct_0(B_24)='#skF_1'(A_25, B_24) | v1_tex_2(B_24, A_25) | ~m1_pre_topc(B_24, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.76/1.32  tff(c_69, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_62])).
% 1.76/1.32  tff(c_72, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_10, c_69])).
% 1.76/1.32  tff(c_77, plain, (![A_26, B_27]: (~v1_subset_1('#skF_1'(A_26, B_27), u1_struct_0(A_26)) | v1_tex_2(B_27, A_26) | ~m1_pre_topc(B_27, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.76/1.32  tff(c_80, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72, c_77])).
% 1.76/1.32  tff(c_85, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_63, c_80])).
% 1.76/1.32  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_85])).
% 1.76/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.32  
% 1.76/1.32  Inference rules
% 1.76/1.32  ----------------------
% 1.76/1.32  #Ref     : 0
% 1.76/1.32  #Sup     : 13
% 1.76/1.32  #Fact    : 0
% 1.76/1.32  #Define  : 0
% 1.76/1.32  #Split   : 2
% 1.76/1.32  #Chain   : 0
% 1.76/1.32  #Close   : 0
% 1.76/1.32  
% 1.76/1.32  Ordering : KBO
% 1.76/1.32  
% 1.76/1.32  Simplification rules
% 1.76/1.32  ----------------------
% 1.76/1.32  #Subsume      : 2
% 1.76/1.32  #Demod        : 12
% 1.76/1.32  #Tautology    : 7
% 1.76/1.32  #SimpNegUnit  : 4
% 1.76/1.32  #BackRed      : 0
% 1.76/1.32  
% 1.76/1.32  #Partial instantiations: 0
% 1.76/1.32  #Strategies tried      : 1
% 1.76/1.32  
% 1.76/1.32  Timing (in seconds)
% 1.76/1.32  ----------------------
% 1.98/1.32  Preprocessing        : 0.32
% 1.98/1.32  Parsing              : 0.16
% 1.98/1.32  CNF conversion       : 0.02
% 1.98/1.32  Main loop            : 0.11
% 1.98/1.32  Inferencing          : 0.04
% 1.98/1.32  Reduction            : 0.03
% 1.98/1.32  Demodulation         : 0.02
% 1.98/1.33  BG Simplification    : 0.01
% 1.98/1.33  Subsumption          : 0.01
% 1.98/1.33  Abstraction          : 0.01
% 1.98/1.33  MUC search           : 0.00
% 1.98/1.33  Cooper               : 0.00
% 1.98/1.33  Total                : 0.46
% 1.98/1.33  Index Insertion      : 0.00
% 1.98/1.33  Index Deletion       : 0.00
% 1.98/1.33  Index Matching       : 0.00
% 1.98/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
