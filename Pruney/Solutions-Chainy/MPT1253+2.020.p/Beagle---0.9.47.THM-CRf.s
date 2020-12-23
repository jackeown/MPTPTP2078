%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:55 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 148 expanded)
%              Number of leaves         :   23 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 342 expanded)
%              Number of equality atoms :   16 (  43 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_62,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_18,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k2_tops_1(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k2_pre_topc(A_23,B_24) = B_24
      | ~ v4_pre_topc(B_24,A_23)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_26])).

tff(c_36,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_32])).

tff(c_88,plain,(
    ! [A_32,B_33] :
      ( k4_subset_1(u1_struct_0(A_32),B_33,k2_tops_1(A_32,B_33)) = k2_pre_topc(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_92,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_96,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36,c_92])).

tff(c_112,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(k3_subset_1(A_40,k4_subset_1(A_40,B_41,C_42)),k3_subset_1(A_40,B_41))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_112])).

tff(c_126,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_121])).

tff(c_127,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_131,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_127])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_131])).

tff(c_137,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_41,plain,(
    ! [A_25,C_26,B_27] :
      ( k4_subset_1(A_25,C_26,B_27) = k4_subset_1(A_25,B_27,C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(A_25))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [B_28] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_28,'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_41])).

tff(c_52,plain,(
    ! [B_16] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_16),'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_16))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_48])).

tff(c_61,plain,(
    ! [B_29] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_29),'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_29))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_52])).

tff(c_72,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_97,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_72])).

tff(c_118,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_112])).

tff(c_124,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_118])).

tff(c_196,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_124])).

tff(c_4,plain,(
    ! [B_5,C_7,A_4] :
      ( r1_tarski(B_5,C_7)
      | ~ r1_tarski(k3_subset_1(A_4,C_7),k3_subset_1(A_4,B_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_199,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_196,c_4])).

tff(c_202,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_22,c_199])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.27  
% 2.33/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.28  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.33/1.28  
% 2.33/1.28  %Foreground sorts:
% 2.33/1.28  
% 2.33/1.28  
% 2.33/1.28  %Background operators:
% 2.33/1.28  
% 2.33/1.28  
% 2.33/1.28  %Foreground operators:
% 2.33/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.28  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.33/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.33/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.33/1.28  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.33/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.33/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.33/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.33/1.28  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.33/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.28  
% 2.33/1.29  tff(f_85, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 2.33/1.29  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.33/1.29  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.33/1.29  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 2.33/1.29  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 2.33/1.29  tff(f_31, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 2.33/1.29  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.33/1.29  tff(c_18, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.33/1.29  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.33/1.29  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.33/1.29  tff(c_14, plain, (![A_15, B_16]: (m1_subset_1(k2_tops_1(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.33/1.29  tff(c_20, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.33/1.29  tff(c_26, plain, (![A_23, B_24]: (k2_pre_topc(A_23, B_24)=B_24 | ~v4_pre_topc(B_24, A_23) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.33/1.29  tff(c_32, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_26])).
% 2.33/1.29  tff(c_36, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_32])).
% 2.33/1.29  tff(c_88, plain, (![A_32, B_33]: (k4_subset_1(u1_struct_0(A_32), B_33, k2_tops_1(A_32, B_33))=k2_pre_topc(A_32, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.29  tff(c_92, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_88])).
% 2.33/1.29  tff(c_96, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_36, c_92])).
% 2.33/1.29  tff(c_112, plain, (![A_40, B_41, C_42]: (r1_tarski(k3_subset_1(A_40, k4_subset_1(A_40, B_41, C_42)), k3_subset_1(A_40, B_41)) | ~m1_subset_1(C_42, k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.29  tff(c_121, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_112])).
% 2.33/1.29  tff(c_126, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_121])).
% 2.33/1.29  tff(c_127, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_126])).
% 2.33/1.29  tff(c_131, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_127])).
% 2.33/1.29  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_131])).
% 2.33/1.29  tff(c_137, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_126])).
% 2.33/1.29  tff(c_41, plain, (![A_25, C_26, B_27]: (k4_subset_1(A_25, C_26, B_27)=k4_subset_1(A_25, B_27, C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(A_25)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.29  tff(c_48, plain, (![B_28]: (k4_subset_1(u1_struct_0('#skF_1'), B_28, '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_41])).
% 2.33/1.29  tff(c_52, plain, (![B_16]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_16), '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_16)) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_48])).
% 2.33/1.29  tff(c_61, plain, (![B_29]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_29), '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_29)) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_52])).
% 2.33/1.29  tff(c_72, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_61])).
% 2.33/1.29  tff(c_97, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_72])).
% 2.33/1.29  tff(c_118, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_97, c_112])).
% 2.33/1.29  tff(c_124, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_118])).
% 2.33/1.29  tff(c_196, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_124])).
% 2.33/1.29  tff(c_4, plain, (![B_5, C_7, A_4]: (r1_tarski(B_5, C_7) | ~r1_tarski(k3_subset_1(A_4, C_7), k3_subset_1(A_4, B_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.33/1.29  tff(c_199, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_196, c_4])).
% 2.33/1.29  tff(c_202, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_22, c_199])).
% 2.33/1.29  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_202])).
% 2.33/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.29  
% 2.33/1.29  Inference rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Ref     : 0
% 2.33/1.29  #Sup     : 39
% 2.33/1.29  #Fact    : 0
% 2.33/1.29  #Define  : 0
% 2.33/1.29  #Split   : 4
% 2.33/1.29  #Chain   : 0
% 2.33/1.29  #Close   : 0
% 2.33/1.29  
% 2.33/1.29  Ordering : KBO
% 2.33/1.29  
% 2.33/1.29  Simplification rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Subsume      : 0
% 2.33/1.29  #Demod        : 25
% 2.33/1.29  #Tautology    : 16
% 2.33/1.29  #SimpNegUnit  : 2
% 2.33/1.29  #BackRed      : 1
% 2.33/1.29  
% 2.33/1.29  #Partial instantiations: 0
% 2.33/1.29  #Strategies tried      : 1
% 2.33/1.29  
% 2.33/1.29  Timing (in seconds)
% 2.33/1.29  ----------------------
% 2.33/1.29  Preprocessing        : 0.31
% 2.33/1.29  Parsing              : 0.17
% 2.33/1.29  CNF conversion       : 0.02
% 2.33/1.29  Main loop            : 0.21
% 2.33/1.29  Inferencing          : 0.08
% 2.33/1.29  Reduction            : 0.06
% 2.33/1.29  Demodulation         : 0.05
% 2.33/1.29  BG Simplification    : 0.01
% 2.33/1.29  Subsumption          : 0.04
% 2.33/1.29  Abstraction          : 0.01
% 2.33/1.30  MUC search           : 0.00
% 2.33/1.30  Cooper               : 0.00
% 2.33/1.30  Total                : 0.55
% 2.33/1.30  Index Insertion      : 0.00
% 2.33/1.30  Index Deletion       : 0.00
% 2.33/1.30  Index Matching       : 0.00
% 2.33/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
