%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:04 EST 2020

% Result     : Theorem 6.27s
% Output     : CNFRefutation 6.27s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 119 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 ( 217 expanded)
%              Number of equality atoms :   11 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_81,plain,(
    ! [A_39,B_40,C_41] :
      ( k9_subset_1(A_39,B_40,C_41) = k3_xboole_0(B_40,C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_138,plain,(
    ! [B_47] : k9_subset_1(u1_struct_0('#skF_1'),B_47,'#skF_2') = k3_xboole_0(B_47,'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_81])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_144,plain,(
    ! [B_47] :
      ( m1_subset_1(k3_xboole_0(B_47,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_8])).

tff(c_150,plain,(
    ! [B_47] : m1_subset_1(k3_xboole_0(B_47,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_144])).

tff(c_24,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    ! [B_29,A_30] : r1_tarski(k3_xboole_0(B_29,A_30),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4])).

tff(c_14,plain,(
    ! [A_16,B_20,C_22] :
      ( r1_tarski(k2_pre_topc(A_16,B_20),k2_pre_topc(A_16,C_22))
      | ~ r1_tarski(B_20,C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,k3_xboole_0(B_6,C_7))
      | ~ r1_tarski(A_5,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_134,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k2_pre_topc(A_45,B_46),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] :
      ( k9_subset_1(A_11,B_12,C_13) = k3_xboole_0(B_12,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_555,plain,(
    ! [A_81,B_82,B_83] :
      ( k9_subset_1(u1_struct_0(A_81),B_82,k2_pre_topc(A_81,B_83)) = k3_xboole_0(B_82,k2_pre_topc(A_81,B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_134,c_10])).

tff(c_586,plain,(
    ! [B_82] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_82,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_82,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_555])).

tff(c_629,plain,(
    ! [B_82] : k9_subset_1(u1_struct_0('#skF_1'),B_82,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_82,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_586])).

tff(c_89,plain,(
    ! [B_40] : k9_subset_1(u1_struct_0('#skF_1'),B_40,'#skF_3') = k3_xboole_0(B_40,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_81])).

tff(c_16,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_91,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_16])).

tff(c_92,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_91])).

tff(c_933,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_92])).

tff(c_934,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_933])).

tff(c_1800,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_934])).

tff(c_5780,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1800])).

tff(c_5783,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_5780])).

tff(c_5787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_150,c_18,c_4,c_5783])).

tff(c_5788,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1800])).

tff(c_5792,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_5788])).

tff(c_5796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_150,c_20,c_39,c_5792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:03:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.27/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.28  
% 6.27/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.28  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.27/2.28  
% 6.27/2.28  %Foreground sorts:
% 6.27/2.28  
% 6.27/2.28  
% 6.27/2.28  %Background operators:
% 6.27/2.28  
% 6.27/2.28  
% 6.27/2.28  %Foreground operators:
% 6.27/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.27/2.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.27/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.27/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.27/2.28  tff('#skF_3', type, '#skF_3': $i).
% 6.27/2.28  tff('#skF_1', type, '#skF_1': $i).
% 6.27/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.27/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.27/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.27/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.27/2.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.27/2.28  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.27/2.28  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.27/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.27/2.28  
% 6.27/2.29  tff(f_72, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 6.27/2.29  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.27/2.29  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 6.27/2.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.27/2.29  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.27/2.29  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 6.27/2.29  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 6.27/2.29  tff(f_49, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.27/2.29  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.27/2.29  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.27/2.29  tff(c_81, plain, (![A_39, B_40, C_41]: (k9_subset_1(A_39, B_40, C_41)=k3_xboole_0(B_40, C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.27/2.29  tff(c_138, plain, (![B_47]: (k9_subset_1(u1_struct_0('#skF_1'), B_47, '#skF_2')=k3_xboole_0(B_47, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_81])).
% 6.27/2.29  tff(c_8, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.27/2.29  tff(c_144, plain, (![B_47]: (m1_subset_1(k3_xboole_0(B_47, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_138, c_8])).
% 6.27/2.29  tff(c_150, plain, (![B_47]: (m1_subset_1(k3_xboole_0(B_47, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_144])).
% 6.27/2.29  tff(c_24, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.27/2.29  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.27/2.29  tff(c_39, plain, (![B_29, A_30]: (r1_tarski(k3_xboole_0(B_29, A_30), A_30))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4])).
% 6.27/2.29  tff(c_14, plain, (![A_16, B_20, C_22]: (r1_tarski(k2_pre_topc(A_16, B_20), k2_pre_topc(A_16, C_22)) | ~r1_tarski(B_20, C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.27/2.29  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.27/2.29  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, k3_xboole_0(B_6, C_7)) | ~r1_tarski(A_5, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.27/2.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.27/2.29  tff(c_134, plain, (![A_45, B_46]: (m1_subset_1(k2_pre_topc(A_45, B_46), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.27/2.29  tff(c_10, plain, (![A_11, B_12, C_13]: (k9_subset_1(A_11, B_12, C_13)=k3_xboole_0(B_12, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.27/2.29  tff(c_555, plain, (![A_81, B_82, B_83]: (k9_subset_1(u1_struct_0(A_81), B_82, k2_pre_topc(A_81, B_83))=k3_xboole_0(B_82, k2_pre_topc(A_81, B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_134, c_10])).
% 6.27/2.29  tff(c_586, plain, (![B_82]: (k9_subset_1(u1_struct_0('#skF_1'), B_82, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_82, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_555])).
% 6.27/2.29  tff(c_629, plain, (![B_82]: (k9_subset_1(u1_struct_0('#skF_1'), B_82, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_82, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_586])).
% 6.27/2.29  tff(c_89, plain, (![B_40]: (k9_subset_1(u1_struct_0('#skF_1'), B_40, '#skF_3')=k3_xboole_0(B_40, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_81])).
% 6.27/2.29  tff(c_16, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.27/2.29  tff(c_91, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_16])).
% 6.27/2.29  tff(c_92, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_91])).
% 6.27/2.29  tff(c_933, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_629, c_92])).
% 6.27/2.29  tff(c_934, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_933])).
% 6.27/2.29  tff(c_1800, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_934])).
% 6.27/2.29  tff(c_5780, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1800])).
% 6.27/2.29  tff(c_5783, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_5780])).
% 6.27/2.29  tff(c_5787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_150, c_18, c_4, c_5783])).
% 6.27/2.29  tff(c_5788, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1800])).
% 6.27/2.29  tff(c_5792, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_5788])).
% 6.27/2.29  tff(c_5796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_150, c_20, c_39, c_5792])).
% 6.27/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.29  
% 6.27/2.29  Inference rules
% 6.27/2.29  ----------------------
% 6.27/2.29  #Ref     : 0
% 6.27/2.29  #Sup     : 1265
% 6.27/2.29  #Fact    : 0
% 6.27/2.29  #Define  : 0
% 6.27/2.29  #Split   : 3
% 6.27/2.29  #Chain   : 0
% 6.27/2.29  #Close   : 0
% 6.27/2.29  
% 6.27/2.29  Ordering : KBO
% 6.27/2.29  
% 6.27/2.29  Simplification rules
% 6.27/2.29  ----------------------
% 6.27/2.29  #Subsume      : 54
% 6.27/2.29  #Demod        : 981
% 6.27/2.29  #Tautology    : 727
% 6.27/2.29  #SimpNegUnit  : 0
% 6.27/2.29  #BackRed      : 2
% 6.27/2.29  
% 6.27/2.29  #Partial instantiations: 0
% 6.27/2.29  #Strategies tried      : 1
% 6.27/2.29  
% 6.27/2.29  Timing (in seconds)
% 6.27/2.29  ----------------------
% 6.49/2.30  Preprocessing        : 0.30
% 6.49/2.30  Parsing              : 0.16
% 6.49/2.30  CNF conversion       : 0.02
% 6.49/2.30  Main loop            : 1.23
% 6.49/2.30  Inferencing          : 0.36
% 6.49/2.30  Reduction            : 0.60
% 6.49/2.30  Demodulation         : 0.52
% 6.49/2.30  BG Simplification    : 0.04
% 6.49/2.30  Subsumption          : 0.16
% 6.49/2.30  Abstraction          : 0.07
% 6.49/2.30  MUC search           : 0.00
% 6.49/2.30  Cooper               : 0.00
% 6.49/2.30  Total                : 1.56
% 6.49/2.30  Index Insertion      : 0.00
% 6.49/2.30  Index Deletion       : 0.00
% 6.49/2.30  Index Matching       : 0.00
% 6.49/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
