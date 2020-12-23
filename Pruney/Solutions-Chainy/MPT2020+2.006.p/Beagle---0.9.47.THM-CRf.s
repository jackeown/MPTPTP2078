%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:10 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 164 expanded)
%              Number of equality atoms :    5 (  26 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v1_tops_2(C,A) )
                     => v1_tops_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_9)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v1_tops_2(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                   => ( D = B
                     => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_19] :
      ( m1_pre_topc(A_19,A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    ! [A_32,B_33] :
      ( m1_pre_topc(A_32,g1_pre_topc(u1_struct_0(B_33),u1_pre_topc(B_33)))
      | ~ m1_pre_topc(A_32,B_33)
      | ~ l1_pre_topc(B_33)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_39,plain,(
    ! [A_32] :
      ( m1_pre_topc(A_32,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_32,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_36])).

tff(c_41,plain,(
    ! [A_32] :
      ( m1_pre_topc(A_32,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_32,'#skF_2')
      | ~ l1_pre_topc(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_39])).

tff(c_43,plain,(
    ! [A_35,B_36] :
      ( m1_pre_topc(A_35,B_36)
      | ~ m1_pre_topc(A_35,g1_pre_topc(u1_struct_0(B_36),u1_pre_topc(B_36)))
      | ~ l1_pre_topc(B_36)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    ! [A_32] :
      ( m1_pre_topc(A_32,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_32,'#skF_2')
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_41,c_43])).

tff(c_64,plain,(
    ! [A_37] :
      ( m1_pre_topc(A_37,'#skF_1')
      | ~ m1_pre_topc(A_37,'#skF_2')
      | ~ l1_pre_topc(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_46])).

tff(c_68,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_71,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_68])).

tff(c_14,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    v1_tops_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    v1_tops_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_25,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_10,plain,(
    ~ v1_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_89,plain,(
    ! [D_39,C_40,A_41] :
      ( v1_tops_2(D_39,C_40)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_40))))
      | ~ v1_tops_2(D_39,A_41)
      | ~ m1_pre_topc(C_40,A_41)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41))))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    ! [A_41] :
      ( v1_tops_2('#skF_4','#skF_2')
      | ~ v1_tops_2('#skF_4',A_41)
      | ~ m1_pre_topc('#skF_2',A_41)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41))))
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_18,c_89])).

tff(c_105,plain,(
    ! [A_43] :
      ( ~ v1_tops_2('#skF_4',A_43)
      | ~ m1_pre_topc('#skF_2',A_43)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_43))))
      | ~ l1_pre_topc(A_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_91])).

tff(c_111,plain,
    ( ~ v1_tops_2('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_25,c_105])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_71,c_26,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 16:36:47 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.17  
% 1.76/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.17  %$ v1_tops_2 > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.76/1.17  
% 1.76/1.17  %Foreground sorts:
% 1.76/1.17  
% 1.76/1.17  
% 1.76/1.17  %Background operators:
% 1.76/1.17  
% 1.76/1.17  
% 1.76/1.17  %Foreground operators:
% 1.76/1.17  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.76/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.17  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.76/1.17  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 1.76/1.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.76/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.76/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.76/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.17  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.76/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.76/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.76/1.17  
% 2.00/1.19  tff(f_75, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v1_tops_2(C, A)) => v1_tops_2(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_waybel_9)).
% 2.00/1.19  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.00/1.19  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 2.00/1.19  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_2)).
% 2.00/1.19  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.19  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.19  tff(c_8, plain, (![A_19]: (m1_pre_topc(A_19, A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.00/1.19  tff(c_16, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.19  tff(c_36, plain, (![A_32, B_33]: (m1_pre_topc(A_32, g1_pre_topc(u1_struct_0(B_33), u1_pre_topc(B_33))) | ~m1_pre_topc(A_32, B_33) | ~l1_pre_topc(B_33) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.00/1.19  tff(c_39, plain, (![A_32]: (m1_pre_topc(A_32, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_32, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_32))), inference(superposition, [status(thm), theory('equality')], [c_16, c_36])).
% 2.00/1.19  tff(c_41, plain, (![A_32]: (m1_pre_topc(A_32, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_32, '#skF_2') | ~l1_pre_topc(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_39])).
% 2.00/1.19  tff(c_43, plain, (![A_35, B_36]: (m1_pre_topc(A_35, B_36) | ~m1_pre_topc(A_35, g1_pre_topc(u1_struct_0(B_36), u1_pre_topc(B_36))) | ~l1_pre_topc(B_36) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.00/1.19  tff(c_46, plain, (![A_32]: (m1_pre_topc(A_32, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_32, '#skF_2') | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_41, c_43])).
% 2.00/1.19  tff(c_64, plain, (![A_37]: (m1_pre_topc(A_37, '#skF_1') | ~m1_pre_topc(A_37, '#skF_2') | ~l1_pre_topc(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_46])).
% 2.00/1.19  tff(c_68, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_64])).
% 2.00/1.19  tff(c_71, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_68])).
% 2.00/1.19  tff(c_14, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.19  tff(c_12, plain, (v1_tops_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.19  tff(c_26, plain, (v1_tops_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12])).
% 2.00/1.19  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.19  tff(c_25, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 2.00/1.19  tff(c_10, plain, (~v1_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.19  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.19  tff(c_89, plain, (![D_39, C_40, A_41]: (v1_tops_2(D_39, C_40) | ~m1_subset_1(D_39, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_40)))) | ~v1_tops_2(D_39, A_41) | ~m1_pre_topc(C_40, A_41) | ~m1_subset_1(D_39, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41)))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.00/1.19  tff(c_91, plain, (![A_41]: (v1_tops_2('#skF_4', '#skF_2') | ~v1_tops_2('#skF_4', A_41) | ~m1_pre_topc('#skF_2', A_41) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41)))) | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_18, c_89])).
% 2.00/1.19  tff(c_105, plain, (![A_43]: (~v1_tops_2('#skF_4', A_43) | ~m1_pre_topc('#skF_2', A_43) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_43)))) | ~l1_pre_topc(A_43))), inference(negUnitSimplification, [status(thm)], [c_10, c_91])).
% 2.00/1.19  tff(c_111, plain, (~v1_tops_2('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_25, c_105])).
% 2.00/1.19  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_71, c_26, c_111])).
% 2.00/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.19  
% 2.00/1.19  Inference rules
% 2.00/1.19  ----------------------
% 2.00/1.19  #Ref     : 0
% 2.00/1.19  #Sup     : 18
% 2.00/1.19  #Fact    : 0
% 2.00/1.19  #Define  : 0
% 2.00/1.19  #Split   : 1
% 2.00/1.19  #Chain   : 0
% 2.00/1.19  #Close   : 0
% 2.00/1.19  
% 2.00/1.19  Ordering : KBO
% 2.00/1.19  
% 2.00/1.19  Simplification rules
% 2.00/1.19  ----------------------
% 2.00/1.19  #Subsume      : 1
% 2.00/1.19  #Demod        : 12
% 2.00/1.19  #Tautology    : 8
% 2.00/1.19  #SimpNegUnit  : 1
% 2.00/1.19  #BackRed      : 0
% 2.00/1.19  
% 2.00/1.19  #Partial instantiations: 0
% 2.00/1.19  #Strategies tried      : 1
% 2.00/1.19  
% 2.00/1.19  Timing (in seconds)
% 2.00/1.19  ----------------------
% 2.00/1.19  Preprocessing        : 0.29
% 2.00/1.19  Parsing              : 0.16
% 2.00/1.19  CNF conversion       : 0.02
% 2.00/1.19  Main loop            : 0.13
% 2.00/1.19  Inferencing          : 0.05
% 2.00/1.19  Reduction            : 0.04
% 2.00/1.19  Demodulation         : 0.03
% 2.00/1.19  BG Simplification    : 0.01
% 2.00/1.19  Subsumption          : 0.03
% 2.00/1.19  Abstraction          : 0.01
% 2.00/1.19  MUC search           : 0.00
% 2.00/1.19  Cooper               : 0.00
% 2.00/1.19  Total                : 0.45
% 2.00/1.19  Index Insertion      : 0.00
% 2.00/1.19  Index Deletion       : 0.00
% 2.00/1.19  Index Matching       : 0.00
% 2.00/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
