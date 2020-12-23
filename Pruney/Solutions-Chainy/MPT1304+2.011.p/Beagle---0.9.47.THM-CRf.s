%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:50 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
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
%$ v1_tops_2 > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

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
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tops_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( v1_tops_2(B,A)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
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
      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A_28)),B_29,C_30),A_28)
      | ~ v1_tops_2(B_29,A_28)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28))))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28))))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    ! [B_21] :
      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_21,'#skF_3'),'#skF_1')
      | ~ v1_tops_2(B_21,'#skF_1')
      | ~ m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_55])).

tff(c_67,plain,(
    ! [B_21] :
      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_21,'#skF_3'),'#skF_1')
      | ~ v1_tops_2(B_21,'#skF_1')
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
      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_31,'#skF_3'),'#skF_1')
      | ~ v1_tops_2(B_31,'#skF_1')
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_8,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_86,plain,
    ( ~ v1_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_83,c_8])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.25  
% 1.75/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.25  %$ v1_tops_2 > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.75/1.25  
% 1.75/1.25  %Foreground sorts:
% 1.75/1.25  
% 1.75/1.25  
% 1.75/1.25  %Background operators:
% 1.75/1.25  
% 1.75/1.25  
% 1.75/1.25  %Foreground operators:
% 1.75/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.25  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 1.75/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.75/1.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.75/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.25  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 1.75/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.75/1.25  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 1.75/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.25  
% 1.75/1.26  tff(f_61, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tops_2)).
% 1.75/1.26  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.75/1.26  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 1.75/1.26  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tops_2)).
% 1.75/1.26  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.75/1.26  tff(c_10, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.75/1.26  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.75/1.26  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.26  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.75/1.26  tff(c_18, plain, (![A_20, B_21, C_22]: (k9_subset_1(A_20, B_21, k3_subset_1(A_20, C_22))=k7_subset_1(A_20, B_21, C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.75/1.26  tff(c_26, plain, (![B_21]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_21, k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'))=k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_21, '#skF_3') | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(resolution, [status(thm)], [c_12, c_18])).
% 1.75/1.26  tff(c_55, plain, (![A_28, B_29, C_30]: (v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A_28)), B_29, C_30), A_28) | ~v1_tops_2(B_29, A_28) | ~m1_subset_1(C_30, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28)))) | ~m1_subset_1(B_29, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28)))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.75/1.26  tff(c_58, plain, (![B_21]: (v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_21, '#skF_3'), '#skF_1') | ~v1_tops_2(B_21, '#skF_1') | ~m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_55])).
% 1.75/1.26  tff(c_67, plain, (![B_21]: (v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_21, '#skF_3'), '#skF_1') | ~v1_tops_2(B_21, '#skF_1') | ~m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 1.75/1.26  tff(c_70, plain, (~m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_67])).
% 1.75/1.26  tff(c_73, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_2, c_70])).
% 1.75/1.26  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_73])).
% 1.75/1.26  tff(c_83, plain, (![B_31]: (v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_31, '#skF_3'), '#skF_1') | ~v1_tops_2(B_31, '#skF_1') | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(splitRight, [status(thm)], [c_67])).
% 1.75/1.26  tff(c_8, plain, (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.75/1.26  tff(c_86, plain, (~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_83, c_8])).
% 1.75/1.26  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_10, c_86])).
% 1.75/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.26  
% 1.75/1.26  Inference rules
% 1.75/1.26  ----------------------
% 1.75/1.26  #Ref     : 0
% 1.75/1.26  #Sup     : 15
% 1.75/1.26  #Fact    : 0
% 1.75/1.26  #Define  : 0
% 1.75/1.26  #Split   : 1
% 1.75/1.26  #Chain   : 0
% 1.75/1.26  #Close   : 0
% 1.75/1.26  
% 1.75/1.26  Ordering : KBO
% 1.75/1.26  
% 1.75/1.26  Simplification rules
% 1.75/1.26  ----------------------
% 1.75/1.26  #Subsume      : 0
% 1.75/1.26  #Demod        : 5
% 1.75/1.26  #Tautology    : 6
% 1.75/1.26  #SimpNegUnit  : 0
% 1.75/1.26  #BackRed      : 0
% 1.75/1.26  
% 1.75/1.26  #Partial instantiations: 0
% 1.75/1.26  #Strategies tried      : 1
% 1.75/1.26  
% 1.75/1.26  Timing (in seconds)
% 1.75/1.26  ----------------------
% 1.75/1.27  Preprocessing        : 0.30
% 1.75/1.27  Parsing              : 0.16
% 1.75/1.27  CNF conversion       : 0.02
% 1.75/1.27  Main loop            : 0.15
% 1.75/1.27  Inferencing          : 0.06
% 1.75/1.27  Reduction            : 0.04
% 1.75/1.27  Demodulation         : 0.03
% 1.75/1.27  BG Simplification    : 0.01
% 1.75/1.27  Subsumption          : 0.03
% 1.75/1.27  Abstraction          : 0.01
% 1.75/1.27  MUC search           : 0.00
% 1.75/1.27  Cooper               : 0.00
% 1.75/1.27  Total                : 0.48
% 2.02/1.27  Index Insertion      : 0.00
% 2.02/1.27  Index Deletion       : 0.00
% 2.02/1.27  Index Matching       : 0.00
% 2.02/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
