%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:47 EST 2020

% Result     : Theorem 10.83s
% Output     : CNFRefutation 10.83s
% Verified   : 
% Statistics : Number of formulae       :   57 (  73 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 114 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_104,plain,(
    ! [A_48,B_49,C_50] :
      ( k7_subset_1(A_48,B_49,C_50) = k4_xboole_0(B_49,C_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_120,plain,(
    ! [C_51] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_51) = k4_xboole_0('#skF_2',C_51) ),
    inference(resolution,[status(thm)],[c_28,c_104])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k7_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_129,plain,(
    ! [C_51] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_51),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_8])).

tff(c_137,plain,(
    ! [C_51] : m1_subset_1(k4_xboole_0('#skF_2',C_51),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_129])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_139,plain,(
    ! [A_52,C_53] : k7_subset_1(A_52,A_52,C_53) = k4_xboole_0(A_52,C_53) ),
    inference(resolution,[status(thm)],[c_31,c_104])).

tff(c_97,plain,(
    ! [A_42,B_43,C_44] :
      ( m1_subset_1(k7_subset_1(A_42,B_43,C_44),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_tarski(k7_subset_1(A_42,B_43,C_44),A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(resolution,[status(thm)],[c_97,c_16])).

tff(c_145,plain,(
    ! [A_52,C_53] :
      ( r1_tarski(k4_xboole_0(A_52,C_53),A_52)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_101])).

tff(c_154,plain,(
    ! [A_52,C_53] : r1_tarski(k4_xboole_0(A_52,C_53),A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_145])).

tff(c_301,plain,(
    ! [B_74,A_75,C_76] :
      ( v1_tops_2(B_74,A_75)
      | ~ v1_tops_2(C_76,A_75)
      | ~ r1_tarski(B_74,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_75))))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_75))))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7808,plain,(
    ! [A_535,C_536,A_537] :
      ( v1_tops_2(k4_xboole_0(A_535,C_536),A_537)
      | ~ v1_tops_2(A_535,A_537)
      | ~ m1_subset_1(A_535,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_537))))
      | ~ m1_subset_1(k4_xboole_0(A_535,C_536),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_537))))
      | ~ l1_pre_topc(A_537) ) ),
    inference(resolution,[status(thm)],[c_154,c_301])).

tff(c_7910,plain,(
    ! [C_51] :
      ( v1_tops_2(k4_xboole_0('#skF_2',C_51),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_137,c_7808])).

tff(c_8010,plain,(
    ! [C_538] : v1_tops_2(k4_xboole_0('#skF_2',C_538),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_7910])).

tff(c_8034,plain,(
    ! [B_2] : v1_tops_2(k3_xboole_0('#skF_2',B_2),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8010])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_190,plain,(
    ! [A_62,B_63,C_64] :
      ( k9_subset_1(A_62,B_63,C_64) = k3_xboole_0(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_210,plain,(
    ! [B_63] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_63,'#skF_3') = k3_xboole_0(B_63,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_190])).

tff(c_22,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_357,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_22])).

tff(c_8037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8034,c_357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.83/4.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.83/4.18  
% 10.83/4.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.83/4.18  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 10.83/4.18  
% 10.83/4.18  %Foreground sorts:
% 10.83/4.18  
% 10.83/4.18  
% 10.83/4.18  %Background operators:
% 10.83/4.18  
% 10.83/4.18  
% 10.83/4.18  %Foreground operators:
% 10.83/4.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.83/4.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.83/4.18  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 10.83/4.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.83/4.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.83/4.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.83/4.18  tff('#skF_2', type, '#skF_2': $i).
% 10.83/4.18  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.83/4.18  tff('#skF_3', type, '#skF_3': $i).
% 10.83/4.18  tff('#skF_1', type, '#skF_1': $i).
% 10.83/4.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.83/4.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.83/4.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.83/4.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.83/4.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.83/4.18  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.83/4.18  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.83/4.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.83/4.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.83/4.18  
% 10.83/4.20  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.83/4.20  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_tops_2)).
% 10.83/4.20  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.83/4.20  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 10.83/4.20  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 10.83/4.20  tff(f_31, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 10.83/4.20  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.83/4.20  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 10.83/4.20  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 10.83/4.20  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.83/4.20  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.83/4.20  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.83/4.20  tff(c_24, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.83/4.20  tff(c_104, plain, (![A_48, B_49, C_50]: (k7_subset_1(A_48, B_49, C_50)=k4_xboole_0(B_49, C_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.83/4.20  tff(c_120, plain, (![C_51]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_51)=k4_xboole_0('#skF_2', C_51))), inference(resolution, [status(thm)], [c_28, c_104])).
% 10.83/4.20  tff(c_8, plain, (![A_5, B_6, C_7]: (m1_subset_1(k7_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.83/4.20  tff(c_129, plain, (![C_51]: (m1_subset_1(k4_xboole_0('#skF_2', C_51), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_120, c_8])).
% 10.83/4.20  tff(c_137, plain, (![C_51]: (m1_subset_1(k4_xboole_0('#skF_2', C_51), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_129])).
% 10.83/4.20  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.83/4.20  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.83/4.20  tff(c_31, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 10.83/4.20  tff(c_139, plain, (![A_52, C_53]: (k7_subset_1(A_52, A_52, C_53)=k4_xboole_0(A_52, C_53))), inference(resolution, [status(thm)], [c_31, c_104])).
% 10.83/4.20  tff(c_97, plain, (![A_42, B_43, C_44]: (m1_subset_1(k7_subset_1(A_42, B_43, C_44), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.83/4.20  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.83/4.20  tff(c_101, plain, (![A_42, B_43, C_44]: (r1_tarski(k7_subset_1(A_42, B_43, C_44), A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(resolution, [status(thm)], [c_97, c_16])).
% 10.83/4.20  tff(c_145, plain, (![A_52, C_53]: (r1_tarski(k4_xboole_0(A_52, C_53), A_52) | ~m1_subset_1(A_52, k1_zfmisc_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_101])).
% 10.83/4.20  tff(c_154, plain, (![A_52, C_53]: (r1_tarski(k4_xboole_0(A_52, C_53), A_52))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_145])).
% 10.83/4.20  tff(c_301, plain, (![B_74, A_75, C_76]: (v1_tops_2(B_74, A_75) | ~v1_tops_2(C_76, A_75) | ~r1_tarski(B_74, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_75)))) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_75)))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.83/4.20  tff(c_7808, plain, (![A_535, C_536, A_537]: (v1_tops_2(k4_xboole_0(A_535, C_536), A_537) | ~v1_tops_2(A_535, A_537) | ~m1_subset_1(A_535, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_537)))) | ~m1_subset_1(k4_xboole_0(A_535, C_536), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_537)))) | ~l1_pre_topc(A_537))), inference(resolution, [status(thm)], [c_154, c_301])).
% 10.83/4.20  tff(c_7910, plain, (![C_51]: (v1_tops_2(k4_xboole_0('#skF_2', C_51), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_137, c_7808])).
% 10.83/4.20  tff(c_8010, plain, (![C_538]: (v1_tops_2(k4_xboole_0('#skF_2', C_538), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_7910])).
% 10.83/4.20  tff(c_8034, plain, (![B_2]: (v1_tops_2(k3_xboole_0('#skF_2', B_2), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8010])).
% 10.83/4.20  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.83/4.20  tff(c_190, plain, (![A_62, B_63, C_64]: (k9_subset_1(A_62, B_63, C_64)=k3_xboole_0(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.83/4.20  tff(c_210, plain, (![B_63]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_63, '#skF_3')=k3_xboole_0(B_63, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_190])).
% 10.83/4.20  tff(c_22, plain, (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.83/4.20  tff(c_357, plain, (~v1_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_22])).
% 10.83/4.20  tff(c_8037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8034, c_357])).
% 10.83/4.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.83/4.20  
% 10.83/4.20  Inference rules
% 10.83/4.20  ----------------------
% 10.83/4.20  #Ref     : 0
% 10.93/4.20  #Sup     : 1896
% 10.93/4.20  #Fact    : 0
% 10.93/4.20  #Define  : 0
% 10.93/4.20  #Split   : 1
% 10.93/4.20  #Chain   : 0
% 10.93/4.20  #Close   : 0
% 10.93/4.20  
% 10.93/4.20  Ordering : KBO
% 10.93/4.20  
% 10.93/4.20  Simplification rules
% 10.93/4.20  ----------------------
% 10.93/4.20  #Subsume      : 18
% 10.93/4.20  #Demod        : 1246
% 10.93/4.20  #Tautology    : 617
% 10.93/4.20  #SimpNegUnit  : 0
% 10.93/4.20  #BackRed      : 2
% 10.93/4.20  
% 10.93/4.20  #Partial instantiations: 0
% 10.93/4.20  #Strategies tried      : 1
% 10.93/4.20  
% 10.93/4.20  Timing (in seconds)
% 10.93/4.20  ----------------------
% 10.93/4.21  Preprocessing        : 0.48
% 10.93/4.21  Parsing              : 0.25
% 10.93/4.21  CNF conversion       : 0.03
% 10.93/4.21  Main loop            : 2.80
% 10.93/4.21  Inferencing          : 0.83
% 10.93/4.21  Reduction            : 1.17
% 10.93/4.21  Demodulation         : 0.96
% 10.93/4.21  BG Simplification    : 0.12
% 10.93/4.21  Subsumption          : 0.47
% 10.93/4.21  Abstraction          : 0.17
% 10.93/4.21  MUC search           : 0.00
% 10.93/4.21  Cooper               : 0.00
% 10.93/4.21  Total                : 3.32
% 10.93/4.21  Index Insertion      : 0.00
% 10.93/4.21  Index Deletion       : 0.00
% 10.93/4.21  Index Matching       : 0.00
% 10.93/4.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
