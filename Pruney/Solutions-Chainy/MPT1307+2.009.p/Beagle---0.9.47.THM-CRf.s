%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:55 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   45 (  56 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  93 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tops_2)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_5,B_6] : k3_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k4_xboole_0(A_5,B_6) ),
    inference(resolution,[status(thm)],[c_6,c_26])).

tff(c_52,plain,(
    ! [A_35,B_36,C_37] :
      ( k9_subset_1(A_35,B_36,C_37) = k3_xboole_0(B_36,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [B_36] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_36,'#skF_2') = k3_xboole_0(B_36,'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_52])).

tff(c_77,plain,(
    ! [A_40,B_41,C_42] :
      ( m1_subset_1(k9_subset_1(A_40,B_41,C_42),k1_zfmisc_1(A_40))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    ! [B_36] :
      ( m1_subset_1(k3_xboole_0(B_36,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_77])).

tff(c_91,plain,(
    ! [B_43] : m1_subset_1(k3_xboole_0(B_43,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_82])).

tff(c_97,plain,(
    ! [B_6] : m1_subset_1(k4_xboole_0('#skF_2',B_6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_91])).

tff(c_213,plain,(
    ! [B_60,A_61,C_62] :
      ( v2_tops_2(B_60,A_61)
      | ~ v2_tops_2(C_62,A_61)
      | ~ r1_tarski(B_60,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61))))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61))))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_644,plain,(
    ! [A_121,B_122,A_123] :
      ( v2_tops_2(k4_xboole_0(A_121,B_122),A_123)
      | ~ v2_tops_2(A_121,A_123)
      | ~ m1_subset_1(A_121,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_123))))
      | ~ m1_subset_1(k4_xboole_0(A_121,B_122),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_123))))
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_6,c_213])).

tff(c_665,plain,(
    ! [B_6] :
      ( v2_tops_2(k4_xboole_0('#skF_2',B_6),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_97,c_644])).

tff(c_686,plain,(
    ! [B_6] : v2_tops_2(k4_xboole_0('#skF_2',B_6),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_665])).

tff(c_107,plain,(
    ! [A_45,B_46,C_47] :
      ( k7_subset_1(A_45,B_46,C_47) = k4_xboole_0(B_46,C_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [C_47] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_47) = k4_xboole_0('#skF_2',C_47) ),
    inference(resolution,[status(thm)],[c_22,c_107])).

tff(c_16,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_146,plain,(
    ~ v2_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_16])).

tff(c_689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:20:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.57  
% 2.98/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.57  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.98/1.57  
% 2.98/1.57  %Foreground sorts:
% 2.98/1.57  
% 2.98/1.57  
% 2.98/1.57  %Background operators:
% 2.98/1.57  
% 2.98/1.57  
% 2.98/1.57  %Foreground operators:
% 2.98/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.98/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.98/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.57  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.57  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.98/1.57  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.57  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.57  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.98/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.57  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.98/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.57  
% 2.98/1.58  tff(f_72, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tops_2)).
% 2.98/1.58  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.98/1.58  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.98/1.58  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.98/1.58  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.98/1.58  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tops_2)).
% 2.98/1.58  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.98/1.58  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.98/1.58  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.98/1.58  tff(c_18, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.98/1.58  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.58  tff(c_26, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.58  tff(c_30, plain, (![A_5, B_6]: (k3_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k4_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_6, c_26])).
% 2.98/1.58  tff(c_52, plain, (![A_35, B_36, C_37]: (k9_subset_1(A_35, B_36, C_37)=k3_xboole_0(B_36, C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.58  tff(c_58, plain, (![B_36]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_36, '#skF_2')=k3_xboole_0(B_36, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_52])).
% 2.98/1.58  tff(c_77, plain, (![A_40, B_41, C_42]: (m1_subset_1(k9_subset_1(A_40, B_41, C_42), k1_zfmisc_1(A_40)) | ~m1_subset_1(C_42, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.58  tff(c_82, plain, (![B_36]: (m1_subset_1(k3_xboole_0(B_36, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_58, c_77])).
% 2.98/1.58  tff(c_91, plain, (![B_43]: (m1_subset_1(k3_xboole_0(B_43, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_82])).
% 2.98/1.58  tff(c_97, plain, (![B_6]: (m1_subset_1(k4_xboole_0('#skF_2', B_6), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_91])).
% 2.98/1.58  tff(c_213, plain, (![B_60, A_61, C_62]: (v2_tops_2(B_60, A_61) | ~v2_tops_2(C_62, A_61) | ~r1_tarski(B_60, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61)))) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61)))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.98/1.58  tff(c_644, plain, (![A_121, B_122, A_123]: (v2_tops_2(k4_xboole_0(A_121, B_122), A_123) | ~v2_tops_2(A_121, A_123) | ~m1_subset_1(A_121, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_123)))) | ~m1_subset_1(k4_xboole_0(A_121, B_122), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_123)))) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_6, c_213])).
% 2.98/1.58  tff(c_665, plain, (![B_6]: (v2_tops_2(k4_xboole_0('#skF_2', B_6), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_97, c_644])).
% 2.98/1.58  tff(c_686, plain, (![B_6]: (v2_tops_2(k4_xboole_0('#skF_2', B_6), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18, c_665])).
% 2.98/1.58  tff(c_107, plain, (![A_45, B_46, C_47]: (k7_subset_1(A_45, B_46, C_47)=k4_xboole_0(B_46, C_47) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.58  tff(c_122, plain, (![C_47]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_47)=k4_xboole_0('#skF_2', C_47))), inference(resolution, [status(thm)], [c_22, c_107])).
% 2.98/1.58  tff(c_16, plain, (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.98/1.58  tff(c_146, plain, (~v2_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_16])).
% 2.98/1.58  tff(c_689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_686, c_146])).
% 2.98/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.58  
% 2.98/1.58  Inference rules
% 2.98/1.58  ----------------------
% 2.98/1.58  #Ref     : 0
% 2.98/1.58  #Sup     : 163
% 2.98/1.58  #Fact    : 0
% 2.98/1.58  #Define  : 0
% 2.98/1.58  #Split   : 0
% 2.98/1.58  #Chain   : 0
% 2.98/1.58  #Close   : 0
% 2.98/1.58  
% 2.98/1.58  Ordering : KBO
% 2.98/1.58  
% 2.98/1.58  Simplification rules
% 2.98/1.58  ----------------------
% 2.98/1.58  #Subsume      : 0
% 2.98/1.58  #Demod        : 66
% 2.98/1.58  #Tautology    : 48
% 2.98/1.58  #SimpNegUnit  : 0
% 2.98/1.58  #BackRed      : 2
% 2.98/1.58  
% 2.98/1.58  #Partial instantiations: 0
% 2.98/1.58  #Strategies tried      : 1
% 2.98/1.58  
% 2.98/1.58  Timing (in seconds)
% 2.98/1.58  ----------------------
% 2.98/1.59  Preprocessing        : 0.34
% 2.98/1.59  Parsing              : 0.18
% 2.98/1.59  CNF conversion       : 0.02
% 2.98/1.59  Main loop            : 0.37
% 2.98/1.59  Inferencing          : 0.14
% 2.98/1.59  Reduction            : 0.13
% 2.98/1.59  Demodulation         : 0.10
% 2.98/1.59  BG Simplification    : 0.02
% 2.98/1.59  Subsumption          : 0.05
% 2.98/1.59  Abstraction          : 0.03
% 2.98/1.59  MUC search           : 0.00
% 2.98/1.59  Cooper               : 0.00
% 2.98/1.59  Total                : 0.74
% 2.98/1.59  Index Insertion      : 0.00
% 2.98/1.59  Index Deletion       : 0.00
% 2.98/1.59  Index Matching       : 0.00
% 2.98/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
