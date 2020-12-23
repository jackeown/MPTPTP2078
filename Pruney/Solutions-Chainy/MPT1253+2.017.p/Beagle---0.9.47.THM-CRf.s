%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:54 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  99 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_30,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_132,plain,(
    ! [A_68,B_69] :
      ( k2_pre_topc(A_68,B_69) = B_69
      | ~ v4_pre_topc(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_135,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_138,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_135])).

tff(c_205,plain,(
    ! [A_85,B_86] :
      ( k4_subset_1(u1_struct_0(A_85),B_86,k2_tops_1(A_85,B_86)) = k2_pre_topc(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_209,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_205])).

tff(c_213,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_138,c_209])).

tff(c_26,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k2_tops_1(A_40,B_41),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_148,plain,(
    ! [A_72,B_73,C_74] :
      ( k4_subset_1(A_72,B_73,C_74) = k2_xboole_0(B_73,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_256,plain,(
    ! [A_101,B_102,B_103] :
      ( k4_subset_1(u1_struct_0(A_101),B_102,k2_tops_1(A_101,B_103)) = k2_xboole_0(B_102,k2_tops_1(A_101,B_103))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_26,c_148])).

tff(c_260,plain,(
    ! [B_103] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_103)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_256])).

tff(c_265,plain,(
    ! [B_104] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_104)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_104))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_260])).

tff(c_272,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_265])).

tff(c_277,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_272])).

tff(c_38,plain,(
    ! [B_48,A_49] : k2_xboole_0(B_48,A_49) = k2_xboole_0(A_49,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_49,B_48] : r1_tarski(A_49,k2_xboole_0(B_48,A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4])).

tff(c_282,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_53])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:01:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  
% 2.26/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.26/1.32  
% 2.26/1.32  %Foreground sorts:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Background operators:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Foreground operators:
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.32  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.26/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.26/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.26/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.26/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.26/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.26/1.32  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.26/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.32  
% 2.43/1.33  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 2.43/1.33  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.43/1.33  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 2.43/1.33  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.43/1.33  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.43/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.43/1.33  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.43/1.33  tff(c_30, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.43/1.33  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.43/1.33  tff(c_32, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.43/1.33  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.43/1.33  tff(c_132, plain, (![A_68, B_69]: (k2_pre_topc(A_68, B_69)=B_69 | ~v4_pre_topc(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.43/1.34  tff(c_135, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_132])).
% 2.43/1.34  tff(c_138, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_135])).
% 2.43/1.34  tff(c_205, plain, (![A_85, B_86]: (k4_subset_1(u1_struct_0(A_85), B_86, k2_tops_1(A_85, B_86))=k2_pre_topc(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.43/1.34  tff(c_209, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_205])).
% 2.43/1.34  tff(c_213, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_138, c_209])).
% 2.43/1.34  tff(c_26, plain, (![A_40, B_41]: (m1_subset_1(k2_tops_1(A_40, B_41), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.43/1.34  tff(c_148, plain, (![A_72, B_73, C_74]: (k4_subset_1(A_72, B_73, C_74)=k2_xboole_0(B_73, C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.43/1.34  tff(c_256, plain, (![A_101, B_102, B_103]: (k4_subset_1(u1_struct_0(A_101), B_102, k2_tops_1(A_101, B_103))=k2_xboole_0(B_102, k2_tops_1(A_101, B_103)) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_26, c_148])).
% 2.43/1.34  tff(c_260, plain, (![B_103]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_103))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_256])).
% 2.43/1.34  tff(c_265, plain, (![B_104]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_104))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_104)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_260])).
% 2.43/1.34  tff(c_272, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_265])).
% 2.43/1.34  tff(c_277, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_213, c_272])).
% 2.43/1.34  tff(c_38, plain, (![B_48, A_49]: (k2_xboole_0(B_48, A_49)=k2_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.43/1.34  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.34  tff(c_53, plain, (![A_49, B_48]: (r1_tarski(A_49, k2_xboole_0(B_48, A_49)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_4])).
% 2.43/1.34  tff(c_282, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_277, c_53])).
% 2.43/1.34  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_282])).
% 2.43/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.34  
% 2.43/1.34  Inference rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Ref     : 0
% 2.43/1.34  #Sup     : 60
% 2.43/1.34  #Fact    : 0
% 2.43/1.34  #Define  : 0
% 2.43/1.34  #Split   : 1
% 2.43/1.34  #Chain   : 0
% 2.43/1.34  #Close   : 0
% 2.43/1.34  
% 2.43/1.34  Ordering : KBO
% 2.43/1.34  
% 2.43/1.34  Simplification rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Subsume      : 2
% 2.43/1.34  #Demod        : 18
% 2.43/1.34  #Tautology    : 37
% 2.43/1.34  #SimpNegUnit  : 1
% 2.43/1.34  #BackRed      : 1
% 2.43/1.34  
% 2.43/1.34  #Partial instantiations: 0
% 2.43/1.34  #Strategies tried      : 1
% 2.43/1.34  
% 2.43/1.34  Timing (in seconds)
% 2.43/1.34  ----------------------
% 2.43/1.34  Preprocessing        : 0.34
% 2.43/1.34  Parsing              : 0.18
% 2.43/1.34  CNF conversion       : 0.02
% 2.43/1.34  Main loop            : 0.23
% 2.43/1.34  Inferencing          : 0.09
% 2.43/1.34  Reduction            : 0.07
% 2.43/1.34  Demodulation         : 0.05
% 2.43/1.34  BG Simplification    : 0.02
% 2.43/1.34  Subsumption          : 0.04
% 2.43/1.34  Abstraction          : 0.02
% 2.43/1.34  MUC search           : 0.00
% 2.43/1.34  Cooper               : 0.00
% 2.43/1.34  Total                : 0.60
% 2.43/1.34  Index Insertion      : 0.00
% 2.43/1.34  Index Deletion       : 0.00
% 2.43/1.34  Index Matching       : 0.00
% 2.43/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
