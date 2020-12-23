%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:21 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   50 (  86 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 ( 121 expanded)
%              Number of equality atoms :   17 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_22,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_25,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_37,plain,(
    ! [A_19] :
      ( u1_struct_0(A_19) = k2_struct_0(A_19)
      | ~ l1_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [A_22] :
      ( u1_struct_0(A_22) = k2_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_18,c_37])).

tff(c_79,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_75])).

tff(c_122,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_pre_topc(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_130,plain,(
    ! [B_34] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_34),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_122])).

tff(c_179,plain,(
    ! [B_40] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_40),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_79,c_130])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_187,plain,(
    ! [B_41] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_41),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_179,c_10])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_190,plain,(
    ! [B_41] :
      ( k2_xboole_0(k2_pre_topc('#skF_1',B_41),k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_187,c_4])).

tff(c_232,plain,(
    ! [B_46] :
      ( k2_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_46)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_190])).

tff(c_246,plain,(
    k2_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_25,c_232])).

tff(c_109,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(B_31,k2_pre_topc(A_32,B_31))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_135,plain,(
    ! [A_35] :
      ( r1_tarski(u1_struct_0(A_35),k2_pre_topc(A_35,u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_25,c_109])).

tff(c_141,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_135])).

tff(c_147,plain,(
    r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_79,c_141])).

tff(c_153,plain,(
    k2_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_147,c_4])).

tff(c_252,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_153])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.26  
% 2.07/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.26  %$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1
% 2.07/1.26  
% 2.07/1.26  %Foreground sorts:
% 2.07/1.26  
% 2.07/1.26  
% 2.07/1.26  %Background operators:
% 2.07/1.26  
% 2.07/1.26  
% 2.07/1.26  %Foreground operators:
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.07/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.07/1.26  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.07/1.26  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.07/1.26  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.07/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.26  
% 2.07/1.28  tff(f_65, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 2.07/1.28  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.07/1.28  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.07/1.28  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.07/1.28  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.07/1.28  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.07/1.28  tff(f_49, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.07/1.28  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.07/1.28  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.07/1.28  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.07/1.28  tff(c_22, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.28  tff(c_6, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.28  tff(c_8, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.28  tff(c_25, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.07/1.28  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.28  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.28  tff(c_18, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.28  tff(c_37, plain, (![A_19]: (u1_struct_0(A_19)=k2_struct_0(A_19) | ~l1_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.28  tff(c_75, plain, (![A_22]: (u1_struct_0(A_22)=k2_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(resolution, [status(thm)], [c_18, c_37])).
% 2.07/1.28  tff(c_79, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_75])).
% 2.07/1.28  tff(c_122, plain, (![A_33, B_34]: (m1_subset_1(k2_pre_topc(A_33, B_34), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.07/1.28  tff(c_130, plain, (![B_34]: (m1_subset_1(k2_pre_topc('#skF_1', B_34), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_122])).
% 2.07/1.28  tff(c_179, plain, (![B_40]: (m1_subset_1(k2_pre_topc('#skF_1', B_40), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_40, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_79, c_130])).
% 2.07/1.28  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.28  tff(c_187, plain, (![B_41]: (r1_tarski(k2_pre_topc('#skF_1', B_41), k2_struct_0('#skF_1')) | ~m1_subset_1(B_41, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_179, c_10])).
% 2.07/1.28  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.28  tff(c_190, plain, (![B_41]: (k2_xboole_0(k2_pre_topc('#skF_1', B_41), k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~m1_subset_1(B_41, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_187, c_4])).
% 2.07/1.28  tff(c_232, plain, (![B_46]: (k2_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_46))=k2_struct_0('#skF_1') | ~m1_subset_1(B_46, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_190])).
% 2.07/1.28  tff(c_246, plain, (k2_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_25, c_232])).
% 2.07/1.28  tff(c_109, plain, (![B_31, A_32]: (r1_tarski(B_31, k2_pre_topc(A_32, B_31)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.28  tff(c_135, plain, (![A_35]: (r1_tarski(u1_struct_0(A_35), k2_pre_topc(A_35, u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_25, c_109])).
% 2.07/1.28  tff(c_141, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_79, c_135])).
% 2.07/1.28  tff(c_147, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_79, c_141])).
% 2.07/1.28  tff(c_153, plain, (k2_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_147, c_4])).
% 2.07/1.28  tff(c_252, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_153])).
% 2.07/1.28  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_252])).
% 2.07/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  Inference rules
% 2.07/1.28  ----------------------
% 2.07/1.28  #Ref     : 0
% 2.07/1.28  #Sup     : 50
% 2.07/1.28  #Fact    : 0
% 2.07/1.28  #Define  : 0
% 2.07/1.28  #Split   : 0
% 2.07/1.28  #Chain   : 0
% 2.07/1.28  #Close   : 0
% 2.07/1.28  
% 2.07/1.28  Ordering : KBO
% 2.07/1.28  
% 2.07/1.28  Simplification rules
% 2.07/1.28  ----------------------
% 2.07/1.28  #Subsume      : 1
% 2.07/1.28  #Demod        : 24
% 2.07/1.28  #Tautology    : 24
% 2.07/1.28  #SimpNegUnit  : 1
% 2.07/1.28  #BackRed      : 1
% 2.07/1.28  
% 2.07/1.28  #Partial instantiations: 0
% 2.07/1.28  #Strategies tried      : 1
% 2.07/1.28  
% 2.07/1.28  Timing (in seconds)
% 2.07/1.28  ----------------------
% 2.23/1.28  Preprocessing        : 0.29
% 2.23/1.28  Parsing              : 0.15
% 2.23/1.28  CNF conversion       : 0.02
% 2.23/1.28  Main loop            : 0.20
% 2.23/1.28  Inferencing          : 0.08
% 2.23/1.28  Reduction            : 0.06
% 2.23/1.28  Demodulation         : 0.05
% 2.23/1.28  BG Simplification    : 0.01
% 2.23/1.28  Subsumption          : 0.04
% 2.23/1.28  Abstraction          : 0.01
% 2.23/1.28  MUC search           : 0.00
% 2.23/1.28  Cooper               : 0.00
% 2.23/1.28  Total                : 0.52
% 2.23/1.28  Index Insertion      : 0.00
% 2.23/1.28  Index Deletion       : 0.00
% 2.23/1.28  Index Matching       : 0.00
% 2.23/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
