%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:53 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   47 (  73 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 149 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tops_2)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_49,plain,(
    ! [C_33,A_34,B_35] :
      ( m1_subset_1(C_33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_34))))
      | ~ r1_tarski(C_33,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_34))))
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    ! [A_36,B_37,A_38] :
      ( m1_subset_1(k3_xboole_0(A_36,B_37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38))))
      | ~ m1_subset_1(A_36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38))))
      | ~ l1_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( k9_subset_1(A_3,B_4,C_5) = k3_xboole_0(B_4,C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_39,B_40,A_41,B_42] :
      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(A_39)),B_40,k3_xboole_0(A_41,B_42)) = k3_xboole_0(B_40,k3_xboole_0(A_41,B_42))
      | ~ m1_subset_1(A_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39))))
      | ~ l1_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_65,plain,(
    ! [B_40,B_42] :
      ( k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_40,k3_xboole_0('#skF_3',B_42)) = k3_xboole_0(B_40,k3_xboole_0('#skF_3',B_42))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_57])).

tff(c_67,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_74,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_74])).

tff(c_80,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_14,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    ! [A_1,B_2,A_34] :
      ( m1_subset_1(k3_xboole_0(A_1,B_2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_34))))
      | ~ m1_subset_1(A_1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_34))))
      | ~ l1_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_101,plain,(
    ! [B_50,A_51,C_52] :
      ( v2_tops_2(B_50,A_51)
      | ~ v2_tops_2(C_52,A_51)
      | ~ r1_tarski(B_50,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_51))))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_51))))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_105,plain,(
    ! [A_53,B_54,A_55] :
      ( v2_tops_2(k3_xboole_0(A_53,B_54),A_55)
      | ~ v2_tops_2(A_53,A_55)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55))))
      | ~ m1_subset_1(k3_xboole_0(A_53,B_54),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55))))
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_2,c_101])).

tff(c_110,plain,(
    ! [A_56,B_57,A_58] :
      ( v2_tops_2(k3_xboole_0(A_56,B_57),A_58)
      | ~ v2_tops_2(A_56,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_58))))
      | ~ l1_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_52,c_105])).

tff(c_116,plain,(
    ! [B_57] :
      ( v2_tops_2(k3_xboole_0('#skF_2',B_57),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_110])).

tff(c_123,plain,(
    ! [B_57] : v2_tops_2(k3_xboole_0('#skF_2',B_57),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_20,c_14,c_116])).

tff(c_23,plain,(
    ! [A_28,B_29,C_30] :
      ( k9_subset_1(A_28,B_29,C_30) = k3_xboole_0(B_29,C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [B_29] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_29,'#skF_3') = k3_xboole_0(B_29,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_23])).

tff(c_12,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n022.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 19:09:25 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.26  
% 1.87/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.26  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.87/1.26  
% 1.87/1.26  %Foreground sorts:
% 1.87/1.26  
% 1.87/1.26  
% 1.87/1.26  %Background operators:
% 1.87/1.26  
% 1.87/1.26  
% 1.87/1.26  %Foreground operators:
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.87/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.26  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 1.87/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.87/1.26  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 1.87/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.26  
% 1.87/1.27  tff(f_72, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tops_2)).
% 1.87/1.27  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.87/1.27  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.87/1.27  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 1.87/1.27  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 1.87/1.27  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 1.87/1.27  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.27  tff(c_6, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.27  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.27  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.27  tff(c_49, plain, (![C_33, A_34, B_35]: (m1_subset_1(C_33, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_34)))) | ~r1_tarski(C_33, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_34)))) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.87/1.27  tff(c_53, plain, (![A_36, B_37, A_38]: (m1_subset_1(k3_xboole_0(A_36, B_37), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38)))) | ~m1_subset_1(A_36, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38)))) | ~l1_struct_0(A_38))), inference(resolution, [status(thm)], [c_2, c_49])).
% 1.87/1.27  tff(c_4, plain, (![A_3, B_4, C_5]: (k9_subset_1(A_3, B_4, C_5)=k3_xboole_0(B_4, C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.27  tff(c_57, plain, (![A_39, B_40, A_41, B_42]: (k9_subset_1(k1_zfmisc_1(u1_struct_0(A_39)), B_40, k3_xboole_0(A_41, B_42))=k3_xboole_0(B_40, k3_xboole_0(A_41, B_42)) | ~m1_subset_1(A_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39)))) | ~l1_struct_0(A_39))), inference(resolution, [status(thm)], [c_53, c_4])).
% 1.87/1.27  tff(c_65, plain, (![B_40, B_42]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_40, k3_xboole_0('#skF_3', B_42))=k3_xboole_0(B_40, k3_xboole_0('#skF_3', B_42)) | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_57])).
% 1.87/1.27  tff(c_67, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_65])).
% 1.87/1.27  tff(c_74, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_67])).
% 1.87/1.27  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_74])).
% 1.87/1.27  tff(c_80, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_65])).
% 1.87/1.27  tff(c_14, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.27  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.27  tff(c_52, plain, (![A_1, B_2, A_34]: (m1_subset_1(k3_xboole_0(A_1, B_2), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_34)))) | ~m1_subset_1(A_1, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_34)))) | ~l1_struct_0(A_34))), inference(resolution, [status(thm)], [c_2, c_49])).
% 1.87/1.27  tff(c_101, plain, (![B_50, A_51, C_52]: (v2_tops_2(B_50, A_51) | ~v2_tops_2(C_52, A_51) | ~r1_tarski(B_50, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_51)))) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_51)))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.27  tff(c_105, plain, (![A_53, B_54, A_55]: (v2_tops_2(k3_xboole_0(A_53, B_54), A_55) | ~v2_tops_2(A_53, A_55) | ~m1_subset_1(A_53, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55)))) | ~m1_subset_1(k3_xboole_0(A_53, B_54), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55)))) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_2, c_101])).
% 1.87/1.27  tff(c_110, plain, (![A_56, B_57, A_58]: (v2_tops_2(k3_xboole_0(A_56, B_57), A_58) | ~v2_tops_2(A_56, A_58) | ~l1_pre_topc(A_58) | ~m1_subset_1(A_56, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_58)))) | ~l1_struct_0(A_58))), inference(resolution, [status(thm)], [c_52, c_105])).
% 1.87/1.27  tff(c_116, plain, (![B_57]: (v2_tops_2(k3_xboole_0('#skF_2', B_57), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_110])).
% 1.87/1.27  tff(c_123, plain, (![B_57]: (v2_tops_2(k3_xboole_0('#skF_2', B_57), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_20, c_14, c_116])).
% 1.87/1.27  tff(c_23, plain, (![A_28, B_29, C_30]: (k9_subset_1(A_28, B_29, C_30)=k3_xboole_0(B_29, C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.27  tff(c_28, plain, (![B_29]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_29, '#skF_3')=k3_xboole_0(B_29, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_23])).
% 1.87/1.27  tff(c_12, plain, (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.27  tff(c_30, plain, (~v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12])).
% 1.87/1.27  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_30])).
% 1.87/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.27  
% 1.87/1.27  Inference rules
% 1.87/1.27  ----------------------
% 1.87/1.27  #Ref     : 0
% 1.87/1.27  #Sup     : 22
% 1.87/1.27  #Fact    : 0
% 1.87/1.27  #Define  : 0
% 1.87/1.27  #Split   : 1
% 1.87/1.27  #Chain   : 0
% 1.87/1.27  #Close   : 0
% 1.87/1.27  
% 1.87/1.27  Ordering : KBO
% 1.87/1.27  
% 1.87/1.27  Simplification rules
% 1.87/1.27  ----------------------
% 1.87/1.27  #Subsume      : 0
% 1.87/1.27  #Demod        : 9
% 1.87/1.27  #Tautology    : 8
% 1.87/1.27  #SimpNegUnit  : 0
% 1.87/1.27  #BackRed      : 2
% 1.87/1.27  
% 1.87/1.27  #Partial instantiations: 0
% 1.87/1.27  #Strategies tried      : 1
% 1.87/1.27  
% 1.87/1.27  Timing (in seconds)
% 1.87/1.27  ----------------------
% 1.87/1.28  Preprocessing        : 0.29
% 1.87/1.28  Parsing              : 0.15
% 1.87/1.28  CNF conversion       : 0.02
% 1.87/1.28  Main loop            : 0.15
% 1.87/1.28  Inferencing          : 0.06
% 1.87/1.28  Reduction            : 0.04
% 1.87/1.28  Demodulation         : 0.03
% 1.87/1.28  BG Simplification    : 0.01
% 1.87/1.28  Subsumption          : 0.02
% 1.87/1.28  Abstraction          : 0.01
% 1.87/1.28  MUC search           : 0.00
% 1.87/1.28  Cooper               : 0.00
% 1.87/1.28  Total                : 0.47
% 1.87/1.28  Index Insertion      : 0.00
% 1.87/1.28  Index Deletion       : 0.00
% 1.87/1.28  Index Matching       : 0.00
% 1.87/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
