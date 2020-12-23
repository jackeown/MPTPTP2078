%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:55 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   35 (  52 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 ( 117 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tops_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( v2_tops_2(B,A)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tops_2)).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] :
      ( k9_subset_1(A_20,B_21,k3_subset_1(A_20,C_22)) = k7_subset_1(A_20,B_21,C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [B_21] :
      ( k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_21,k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3')) = k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_21,'#skF_3')
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_12,c_18])).

tff(c_55,plain,(
    ! [A_28,B_29,C_30] :
      ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A_28)),B_29,C_30),A_28)
      | ~ v2_tops_2(B_29,A_28)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28))))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28))))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    ! [B_21] :
      ( v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_21,'#skF_3'),'#skF_1')
      | ~ v2_tops_2(B_21,'#skF_1')
      | ~ m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_55])).

tff(c_67,plain,(
    ! [B_21] :
      ( v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_21,'#skF_3'),'#skF_1')
      | ~ v2_tops_2(B_21,'#skF_1')
      | ~ m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_70,plain,(
    ~ m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_73,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_2,c_70])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_73])).

tff(c_83,plain,(
    ! [B_31] :
      ( v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_31,'#skF_3'),'#skF_1')
      | ~ v2_tops_2(B_31,'#skF_1')
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_8,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_86,plain,
    ( ~ v2_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_83,c_8])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.17  %$ v2_tops_2 > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.83/1.17  
% 1.83/1.17  %Foreground sorts:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Background operators:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Foreground operators:
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.83/1.17  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.83/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.17  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 1.83/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.83/1.17  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.83/1.17  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 1.83/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.17  
% 1.83/1.18  tff(f_61, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tops_2)).
% 1.83/1.18  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.83/1.18  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 1.83/1.18  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tops_2)).
% 1.83/1.18  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.18  tff(c_10, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.18  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.18  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.18  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.18  tff(c_18, plain, (![A_20, B_21, C_22]: (k9_subset_1(A_20, B_21, k3_subset_1(A_20, C_22))=k7_subset_1(A_20, B_21, C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.83/1.18  tff(c_26, plain, (![B_21]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_21, k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'))=k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_21, '#skF_3') | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(resolution, [status(thm)], [c_12, c_18])).
% 1.83/1.18  tff(c_55, plain, (![A_28, B_29, C_30]: (v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A_28)), B_29, C_30), A_28) | ~v2_tops_2(B_29, A_28) | ~m1_subset_1(C_30, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28)))) | ~m1_subset_1(B_29, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28)))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.83/1.18  tff(c_58, plain, (![B_21]: (v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_21, '#skF_3'), '#skF_1') | ~v2_tops_2(B_21, '#skF_1') | ~m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_55])).
% 1.83/1.18  tff(c_67, plain, (![B_21]: (v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_21, '#skF_3'), '#skF_1') | ~v2_tops_2(B_21, '#skF_1') | ~m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 1.83/1.18  tff(c_70, plain, (~m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_67])).
% 1.83/1.18  tff(c_73, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_2, c_70])).
% 1.83/1.18  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_73])).
% 1.83/1.18  tff(c_83, plain, (![B_31]: (v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_31, '#skF_3'), '#skF_1') | ~v2_tops_2(B_31, '#skF_1') | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(splitRight, [status(thm)], [c_67])).
% 1.83/1.18  tff(c_8, plain, (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.18  tff(c_86, plain, (~v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_83, c_8])).
% 1.83/1.18  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_10, c_86])).
% 1.83/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  Inference rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Ref     : 0
% 1.83/1.18  #Sup     : 15
% 1.83/1.18  #Fact    : 0
% 1.83/1.18  #Define  : 0
% 1.83/1.18  #Split   : 1
% 1.83/1.18  #Chain   : 0
% 1.83/1.18  #Close   : 0
% 1.83/1.18  
% 1.83/1.18  Ordering : KBO
% 1.83/1.18  
% 1.83/1.18  Simplification rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Subsume      : 0
% 1.83/1.18  #Demod        : 5
% 1.83/1.19  #Tautology    : 6
% 1.83/1.19  #SimpNegUnit  : 0
% 1.83/1.19  #BackRed      : 0
% 1.83/1.19  
% 1.83/1.19  #Partial instantiations: 0
% 1.83/1.19  #Strategies tried      : 1
% 1.83/1.19  
% 1.83/1.19  Timing (in seconds)
% 1.83/1.19  ----------------------
% 1.83/1.19  Preprocessing        : 0.27
% 1.83/1.19  Parsing              : 0.15
% 1.83/1.19  CNF conversion       : 0.02
% 1.83/1.19  Main loop            : 0.13
% 1.83/1.19  Inferencing          : 0.06
% 1.83/1.19  Reduction            : 0.03
% 1.83/1.19  Demodulation         : 0.03
% 1.83/1.19  BG Simplification    : 0.01
% 1.83/1.19  Subsumption          : 0.02
% 1.83/1.19  Abstraction          : 0.01
% 1.83/1.19  MUC search           : 0.00
% 1.83/1.19  Cooper               : 0.00
% 1.83/1.19  Total                : 0.42
% 1.83/1.19  Index Insertion      : 0.00
% 1.83/1.19  Index Deletion       : 0.00
% 1.83/1.19  Index Matching       : 0.00
% 1.83/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
