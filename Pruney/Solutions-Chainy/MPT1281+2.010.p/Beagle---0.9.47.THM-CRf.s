%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:14 EST 2020

% Result     : Theorem 6.55s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 114 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
           => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_24,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_606,plain,(
    ! [A_100,B_101] :
      ( k2_tops_1(A_100,k1_tops_1(A_100,B_101)) = k2_tops_1(A_100,B_101)
      | ~ v5_tops_1(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_612,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_606])).

tff(c_617,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_612])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k1_tops_1(A_13,B_14),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_396,plain,(
    ! [A_78,B_79] :
      ( k4_subset_1(u1_struct_0(A_78),B_79,k2_tops_1(A_78,B_79)) = k2_pre_topc(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_731,plain,(
    ! [A_111,B_112] :
      ( k4_subset_1(u1_struct_0(A_111),k1_tops_1(A_111,B_112),k2_tops_1(A_111,k1_tops_1(A_111,B_112))) = k2_pre_topc(A_111,k1_tops_1(A_111,B_112))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_16,c_396])).

tff(c_740,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_731])).

tff(c_744,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_740])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k2_tops_1(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_243,plain,(
    ! [A_62,B_63,C_64] :
      ( k4_subset_1(A_62,B_63,C_64) = k2_xboole_0(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_917,plain,(
    ! [A_124,B_125,B_126] :
      ( k4_subset_1(u1_struct_0(A_124),B_125,k2_tops_1(A_124,B_126)) = k2_xboole_0(B_125,k2_tops_1(A_124,B_126))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_18,c_243])).

tff(c_3703,plain,(
    ! [A_263,B_264,B_265] :
      ( k4_subset_1(u1_struct_0(A_263),k1_tops_1(A_263,B_264),k2_tops_1(A_263,B_265)) = k2_xboole_0(k1_tops_1(A_263,B_264),k2_tops_1(A_263,B_265))
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263) ) ),
    inference(resolution,[status(thm)],[c_16,c_917])).

tff(c_3719,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_3703])).

tff(c_3731,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_28,c_3719])).

tff(c_34,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,A_28) = k2_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_28,B_27] : r1_tarski(A_28,k2_xboole_0(B_27,A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_5197,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3731,c_49])).

tff(c_5213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_5197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:03:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.55/2.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.55/2.39  
% 6.55/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.55/2.39  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 6.55/2.39  
% 6.55/2.39  %Foreground sorts:
% 6.55/2.39  
% 6.55/2.39  
% 6.55/2.39  %Background operators:
% 6.55/2.39  
% 6.55/2.39  
% 6.55/2.39  %Foreground operators:
% 6.55/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.55/2.39  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.55/2.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.55/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.55/2.39  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.55/2.39  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.55/2.39  tff('#skF_2', type, '#skF_2': $i).
% 6.55/2.39  tff('#skF_1', type, '#skF_1': $i).
% 6.55/2.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.55/2.39  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 6.55/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.55/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.55/2.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.55/2.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.55/2.39  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.55/2.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.55/2.39  
% 6.55/2.41  tff(f_85, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 6.55/2.41  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 6.55/2.41  tff(f_53, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.55/2.41  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 6.55/2.41  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.55/2.41  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.55/2.41  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.55/2.41  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.55/2.41  tff(c_24, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.55/2.41  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.55/2.41  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.55/2.41  tff(c_26, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.55/2.41  tff(c_606, plain, (![A_100, B_101]: (k2_tops_1(A_100, k1_tops_1(A_100, B_101))=k2_tops_1(A_100, B_101) | ~v5_tops_1(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.55/2.41  tff(c_612, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_606])).
% 6.55/2.41  tff(c_617, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_612])).
% 6.55/2.41  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(k1_tops_1(A_13, B_14), k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.55/2.41  tff(c_396, plain, (![A_78, B_79]: (k4_subset_1(u1_struct_0(A_78), B_79, k2_tops_1(A_78, B_79))=k2_pre_topc(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.55/2.41  tff(c_731, plain, (![A_111, B_112]: (k4_subset_1(u1_struct_0(A_111), k1_tops_1(A_111, B_112), k2_tops_1(A_111, k1_tops_1(A_111, B_112)))=k2_pre_topc(A_111, k1_tops_1(A_111, B_112)) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(resolution, [status(thm)], [c_16, c_396])).
% 6.55/2.41  tff(c_740, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_617, c_731])).
% 6.55/2.41  tff(c_744, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_740])).
% 6.55/2.41  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(k2_tops_1(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.55/2.41  tff(c_243, plain, (![A_62, B_63, C_64]: (k4_subset_1(A_62, B_63, C_64)=k2_xboole_0(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.55/2.41  tff(c_917, plain, (![A_124, B_125, B_126]: (k4_subset_1(u1_struct_0(A_124), B_125, k2_tops_1(A_124, B_126))=k2_xboole_0(B_125, k2_tops_1(A_124, B_126)) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_18, c_243])).
% 6.55/2.41  tff(c_3703, plain, (![A_263, B_264, B_265]: (k4_subset_1(u1_struct_0(A_263), k1_tops_1(A_263, B_264), k2_tops_1(A_263, B_265))=k2_xboole_0(k1_tops_1(A_263, B_264), k2_tops_1(A_263, B_265)) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_263))) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263))), inference(resolution, [status(thm)], [c_16, c_917])).
% 6.55/2.41  tff(c_3719, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_744, c_3703])).
% 6.55/2.41  tff(c_3731, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_28, c_3719])).
% 6.55/2.41  tff(c_34, plain, (![B_27, A_28]: (k2_xboole_0(B_27, A_28)=k2_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.55/2.41  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.55/2.41  tff(c_49, plain, (![A_28, B_27]: (r1_tarski(A_28, k2_xboole_0(B_27, A_28)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_12])).
% 6.55/2.41  tff(c_5197, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3731, c_49])).
% 6.55/2.41  tff(c_5213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_5197])).
% 6.55/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.55/2.41  
% 6.55/2.41  Inference rules
% 6.55/2.41  ----------------------
% 6.55/2.41  #Ref     : 0
% 6.55/2.41  #Sup     : 1298
% 6.55/2.41  #Fact    : 0
% 6.55/2.41  #Define  : 0
% 6.55/2.41  #Split   : 4
% 6.55/2.41  #Chain   : 0
% 6.55/2.41  #Close   : 0
% 6.55/2.41  
% 6.55/2.41  Ordering : KBO
% 6.55/2.41  
% 6.55/2.41  Simplification rules
% 6.55/2.41  ----------------------
% 6.55/2.41  #Subsume      : 74
% 6.55/2.41  #Demod        : 422
% 6.55/2.41  #Tautology    : 339
% 6.55/2.41  #SimpNegUnit  : 2
% 6.55/2.41  #BackRed      : 1
% 6.55/2.41  
% 6.55/2.41  #Partial instantiations: 0
% 6.55/2.41  #Strategies tried      : 1
% 6.55/2.41  
% 6.55/2.41  Timing (in seconds)
% 6.55/2.41  ----------------------
% 6.55/2.41  Preprocessing        : 0.30
% 6.55/2.41  Parsing              : 0.16
% 6.55/2.41  CNF conversion       : 0.02
% 6.55/2.41  Main loop            : 1.33
% 6.55/2.41  Inferencing          : 0.32
% 6.55/2.41  Reduction            : 0.57
% 6.55/2.41  Demodulation         : 0.48
% 6.55/2.41  BG Simplification    : 0.05
% 6.55/2.41  Subsumption          : 0.31
% 6.55/2.41  Abstraction          : 0.06
% 6.55/2.41  MUC search           : 0.00
% 6.55/2.41  Cooper               : 0.00
% 6.55/2.41  Total                : 1.66
% 6.55/2.41  Index Insertion      : 0.00
% 6.55/2.41  Index Deletion       : 0.00
% 6.55/2.41  Index Matching       : 0.00
% 6.55/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
