%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:50 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 125 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( v1_tops_2(B,A)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k3_subset_1(A_28,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    k4_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3') = k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_38])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78,plain,(
    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_2])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_82,plain,(
    ! [A_32,B_33,C_34] :
      ( k9_subset_1(A_32,B_33,k3_subset_1(A_32,C_34)) = k7_subset_1(A_32,B_33,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,(
    ! [B_33] :
      ( k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_33,k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3')) = k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_33,'#skF_3')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_18,c_82])).

tff(c_181,plain,(
    ! [A_44,B_45,C_46] :
      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A_44)),B_45,C_46),A_44)
      | ~ v1_tops_2(B_45,A_44)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44))))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44))))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_184,plain,(
    ! [B_33] :
      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_33,'#skF_3'),'#skF_1')
      | ~ v1_tops_2(B_33,'#skF_1')
      | ~ m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_181])).

tff(c_186,plain,(
    ! [B_33] :
      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_33,'#skF_3'),'#skF_1')
      | ~ v1_tops_2(B_33,'#skF_1')
      | ~ m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_184])).

tff(c_660,plain,(
    ~ m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_663,plain,(
    ~ r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_660])).

tff(c_667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_663])).

tff(c_686,plain,(
    ! [B_68] :
      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_68,'#skF_3'),'#skF_1')
      | ~ v1_tops_2(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_14,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_689,plain,
    ( ~ v1_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_686,c_14])).

tff(c_693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.71  
% 2.79/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.72  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.79/1.72  
% 2.79/1.72  %Foreground sorts:
% 2.79/1.72  
% 2.79/1.72  
% 2.79/1.72  %Background operators:
% 2.79/1.72  
% 2.79/1.72  
% 2.79/1.72  %Foreground operators:
% 2.79/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.79/1.72  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.79/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.79/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.72  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.79/1.72  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.72  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.79/1.72  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.72  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.79/1.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.79/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.72  
% 2.79/1.73  tff(f_67, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tops_2)).
% 2.79/1.73  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.79/1.73  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.79/1.73  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.73  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 2.79/1.73  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_tops_2)).
% 2.79/1.73  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.73  tff(c_16, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.73  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.73  tff(c_38, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k3_subset_1(A_28, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.73  tff(c_49, plain, (k4_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3')=k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3')), inference(resolution, [status(thm)], [c_18, c_38])).
% 2.79/1.73  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.79/1.73  tff(c_78, plain, (r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_49, c_2])).
% 2.79/1.73  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.79/1.73  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.73  tff(c_82, plain, (![A_32, B_33, C_34]: (k9_subset_1(A_32, B_33, k3_subset_1(A_32, C_34))=k7_subset_1(A_32, B_33, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.79/1.73  tff(c_90, plain, (![B_33]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_33, k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'))=k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_33, '#skF_3') | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(resolution, [status(thm)], [c_18, c_82])).
% 2.79/1.73  tff(c_181, plain, (![A_44, B_45, C_46]: (v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A_44)), B_45, C_46), A_44) | ~v1_tops_2(B_45, A_44) | ~m1_subset_1(C_46, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44)))) | ~m1_subset_1(B_45, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44)))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.79/1.73  tff(c_184, plain, (![B_33]: (v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_33, '#skF_3'), '#skF_1') | ~v1_tops_2(B_33, '#skF_1') | ~m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_90, c_181])).
% 2.79/1.73  tff(c_186, plain, (![B_33]: (v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_33, '#skF_3'), '#skF_1') | ~v1_tops_2(B_33, '#skF_1') | ~m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_184])).
% 2.79/1.73  tff(c_660, plain, (~m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_186])).
% 2.79/1.73  tff(c_663, plain, (~r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_660])).
% 2.79/1.73  tff(c_667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_663])).
% 2.79/1.73  tff(c_686, plain, (![B_68]: (v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_68, '#skF_3'), '#skF_1') | ~v1_tops_2(B_68, '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(splitRight, [status(thm)], [c_186])).
% 2.79/1.73  tff(c_14, plain, (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.73  tff(c_689, plain, (~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_686, c_14])).
% 2.79/1.73  tff(c_693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_689])).
% 2.79/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.73  
% 2.79/1.73  Inference rules
% 2.79/1.73  ----------------------
% 2.79/1.73  #Ref     : 0
% 2.79/1.73  #Sup     : 161
% 2.79/1.73  #Fact    : 0
% 2.79/1.73  #Define  : 0
% 2.79/1.73  #Split   : 1
% 2.79/1.73  #Chain   : 0
% 2.79/1.73  #Close   : 0
% 2.79/1.73  
% 2.79/1.73  Ordering : KBO
% 2.79/1.73  
% 2.79/1.73  Simplification rules
% 2.79/1.73  ----------------------
% 2.79/1.73  #Subsume      : 0
% 2.79/1.73  #Demod        : 84
% 2.79/1.73  #Tautology    : 67
% 2.79/1.73  #SimpNegUnit  : 0
% 2.79/1.73  #BackRed      : 0
% 2.79/1.73  
% 2.79/1.73  #Partial instantiations: 0
% 2.79/1.73  #Strategies tried      : 1
% 2.79/1.73  
% 2.79/1.73  Timing (in seconds)
% 2.79/1.73  ----------------------
% 2.79/1.73  Preprocessing        : 0.46
% 2.79/1.73  Parsing              : 0.24
% 2.79/1.73  CNF conversion       : 0.03
% 2.79/1.73  Main loop            : 0.38
% 2.79/1.73  Inferencing          : 0.14
% 2.79/1.73  Reduction            : 0.13
% 2.79/1.73  Demodulation         : 0.10
% 2.79/1.73  BG Simplification    : 0.02
% 2.79/1.73  Subsumption          : 0.06
% 2.79/1.73  Abstraction          : 0.03
% 2.79/1.73  MUC search           : 0.00
% 2.79/1.73  Cooper               : 0.00
% 2.79/1.73  Total                : 0.87
% 2.79/1.73  Index Insertion      : 0.00
% 2.79/1.73  Index Deletion       : 0.00
% 2.79/1.73  Index Matching       : 0.00
% 2.79/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
