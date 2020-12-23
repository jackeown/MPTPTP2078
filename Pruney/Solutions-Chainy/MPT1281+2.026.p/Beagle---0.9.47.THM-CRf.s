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
% DateTime   : Thu Dec  3 10:22:17 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 175 expanded)
%              Number of leaves         :   27 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 331 expanded)
%              Number of equality atoms :   24 (  70 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_477,plain,(
    ! [A_74,B_75] :
      ( k2_pre_topc(A_74,k1_tops_1(A_74,B_75)) = B_75
      | ~ v5_tops_1(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_497,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_477])).

tff(c_511,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_497])).

tff(c_28,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_512,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_28])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_67,plain,(
    ! [A_38,B_39,C_40] :
      ( k9_subset_1(A_38,B_39,C_40) = k3_xboole_0(B_39,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_151,plain,(
    ! [B_49,B_50,A_51] :
      ( k9_subset_1(B_49,B_50,A_51) = k3_xboole_0(B_50,A_51)
      | ~ r1_tarski(A_51,B_49) ) ),
    inference(resolution,[status(thm)],[c_16,c_67])).

tff(c_165,plain,(
    ! [B_52,B_53] : k9_subset_1(B_52,B_53,B_52) = k3_xboole_0(B_53,B_52) ),
    inference(resolution,[status(thm)],[c_6,c_151])).

tff(c_76,plain,(
    ! [B_39] : k9_subset_1(u1_struct_0('#skF_1'),B_39,'#skF_2') = k3_xboole_0(B_39,'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_67])).

tff(c_96,plain,(
    ! [A_42,C_43,B_44] :
      ( k9_subset_1(A_42,C_43,B_44) = k9_subset_1(A_42,B_44,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    ! [B_44] : k9_subset_1(u1_struct_0('#skF_1'),B_44,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_44) ),
    inference(resolution,[status(thm)],[c_32,c_96])).

tff(c_106,plain,(
    ! [B_44] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_44) = k3_xboole_0(B_44,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_102])).

tff(c_172,plain,(
    k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_106])).

tff(c_58,plain,(
    ! [A_32,B_33,C_34] :
      ( m1_subset_1(k9_subset_1(A_32,B_33,C_34),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_tarski(k9_subset_1(A_32,B_33,C_34),A_32)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32)) ) ),
    inference(resolution,[status(thm)],[c_58,c_14])).

tff(c_229,plain,(
    ! [B_56,B_57] :
      ( r1_tarski(k3_xboole_0(B_56,B_57),B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(B_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_62])).

tff(c_236,plain,
    ( r1_tarski(k3_xboole_0('#skF_2',u1_struct_0('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_229])).

tff(c_253,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_256,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_253])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_256])).

tff(c_262,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k1_tops_1(A_22,B_23),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_318,plain,(
    ! [A_62,B_63] :
      ( k2_pre_topc(A_62,k2_pre_topc(A_62,B_63)) = k2_pre_topc(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2360,plain,(
    ! [A_161,B_162] :
      ( k2_pre_topc(A_161,k2_pre_topc(A_161,k1_tops_1(A_161,B_162))) = k2_pre_topc(A_161,k1_tops_1(A_161,B_162))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_26,c_318])).

tff(c_2392,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2360])).

tff(c_2424,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_511,c_511,c_2392])).

tff(c_20,plain,(
    ! [A_16,B_18] :
      ( k9_subset_1(u1_struct_0(A_16),k2_pre_topc(A_16,B_18),k2_pre_topc(A_16,k3_subset_1(u1_struct_0(A_16),B_18))) = k2_tops_1(A_16,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2429,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2424,c_20])).

tff(c_2433,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_106,c_2429])).

tff(c_175,plain,(
    ! [B_53,B_52] :
      ( r1_tarski(k3_xboole_0(B_53,B_52),B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(B_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_62])).

tff(c_2539,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2433,c_175])).

tff(c_2569,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_2539])).

tff(c_2571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_512,c_2569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.83  
% 4.55/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.83  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.55/1.83  
% 4.55/1.83  %Foreground sorts:
% 4.55/1.83  
% 4.55/1.83  
% 4.55/1.83  %Background operators:
% 4.55/1.83  
% 4.55/1.83  
% 4.55/1.83  %Foreground operators:
% 4.55/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.83  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.55/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.55/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.83  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.55/1.83  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.55/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.55/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.83  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 4.55/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.55/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.55/1.83  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.55/1.83  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.55/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.83  
% 4.55/1.84  tff(f_85, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 4.55/1.84  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 4.55/1.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.55/1.84  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.55/1.84  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.55/1.84  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.55/1.84  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 4.55/1.84  tff(f_75, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.55/1.84  tff(f_53, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 4.55/1.84  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 4.55/1.84  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.55/1.84  tff(c_30, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.55/1.84  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.55/1.84  tff(c_477, plain, (![A_74, B_75]: (k2_pre_topc(A_74, k1_tops_1(A_74, B_75))=B_75 | ~v5_tops_1(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.55/1.84  tff(c_497, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_477])).
% 4.55/1.84  tff(c_511, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_497])).
% 4.55/1.84  tff(c_28, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.55/1.84  tff(c_512, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_511, c_28])).
% 4.55/1.84  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/1.84  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.84  tff(c_67, plain, (![A_38, B_39, C_40]: (k9_subset_1(A_38, B_39, C_40)=k3_xboole_0(B_39, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.55/1.84  tff(c_151, plain, (![B_49, B_50, A_51]: (k9_subset_1(B_49, B_50, A_51)=k3_xboole_0(B_50, A_51) | ~r1_tarski(A_51, B_49))), inference(resolution, [status(thm)], [c_16, c_67])).
% 4.55/1.84  tff(c_165, plain, (![B_52, B_53]: (k9_subset_1(B_52, B_53, B_52)=k3_xboole_0(B_53, B_52))), inference(resolution, [status(thm)], [c_6, c_151])).
% 4.55/1.84  tff(c_76, plain, (![B_39]: (k9_subset_1(u1_struct_0('#skF_1'), B_39, '#skF_2')=k3_xboole_0(B_39, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_67])).
% 4.55/1.84  tff(c_96, plain, (![A_42, C_43, B_44]: (k9_subset_1(A_42, C_43, B_44)=k9_subset_1(A_42, B_44, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.84  tff(c_102, plain, (![B_44]: (k9_subset_1(u1_struct_0('#skF_1'), B_44, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_44))), inference(resolution, [status(thm)], [c_32, c_96])).
% 4.55/1.84  tff(c_106, plain, (![B_44]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_44)=k3_xboole_0(B_44, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_102])).
% 4.55/1.84  tff(c_172, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_106])).
% 4.55/1.84  tff(c_58, plain, (![A_32, B_33, C_34]: (m1_subset_1(k9_subset_1(A_32, B_33, C_34), k1_zfmisc_1(A_32)) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.55/1.84  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.84  tff(c_62, plain, (![A_32, B_33, C_34]: (r1_tarski(k9_subset_1(A_32, B_33, C_34), A_32) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)))), inference(resolution, [status(thm)], [c_58, c_14])).
% 4.55/1.84  tff(c_229, plain, (![B_56, B_57]: (r1_tarski(k3_xboole_0(B_56, B_57), B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(B_57)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_62])).
% 4.55/1.84  tff(c_236, plain, (r1_tarski(k3_xboole_0('#skF_2', u1_struct_0('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_229])).
% 4.55/1.84  tff(c_253, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_236])).
% 4.55/1.84  tff(c_256, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_253])).
% 4.55/1.84  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_256])).
% 4.55/1.84  tff(c_262, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_236])).
% 4.55/1.84  tff(c_26, plain, (![A_22, B_23]: (m1_subset_1(k1_tops_1(A_22, B_23), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.55/1.84  tff(c_318, plain, (![A_62, B_63]: (k2_pre_topc(A_62, k2_pre_topc(A_62, B_63))=k2_pre_topc(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.55/1.84  tff(c_2360, plain, (![A_161, B_162]: (k2_pre_topc(A_161, k2_pre_topc(A_161, k1_tops_1(A_161, B_162)))=k2_pre_topc(A_161, k1_tops_1(A_161, B_162)) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(resolution, [status(thm)], [c_26, c_318])).
% 4.55/1.84  tff(c_2392, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2360])).
% 4.55/1.84  tff(c_2424, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_511, c_511, c_2392])).
% 4.55/1.84  tff(c_20, plain, (![A_16, B_18]: (k9_subset_1(u1_struct_0(A_16), k2_pre_topc(A_16, B_18), k2_pre_topc(A_16, k3_subset_1(u1_struct_0(A_16), B_18)))=k2_tops_1(A_16, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.55/1.84  tff(c_2429, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2424, c_20])).
% 4.55/1.84  tff(c_2433, plain, (k3_xboole_0(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_106, c_2429])).
% 4.55/1.84  tff(c_175, plain, (![B_53, B_52]: (r1_tarski(k3_xboole_0(B_53, B_52), B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(B_52)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_62])).
% 4.55/1.84  tff(c_2539, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2433, c_175])).
% 4.55/1.84  tff(c_2569, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_2539])).
% 4.55/1.84  tff(c_2571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_512, c_2569])).
% 4.55/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.84  
% 4.55/1.84  Inference rules
% 4.55/1.84  ----------------------
% 4.55/1.84  #Ref     : 0
% 4.55/1.84  #Sup     : 684
% 4.55/1.84  #Fact    : 0
% 4.55/1.84  #Define  : 0
% 4.55/1.84  #Split   : 4
% 4.55/1.84  #Chain   : 0
% 4.55/1.84  #Close   : 0
% 4.55/1.84  
% 4.55/1.84  Ordering : KBO
% 4.55/1.84  
% 4.55/1.84  Simplification rules
% 4.55/1.84  ----------------------
% 4.55/1.84  #Subsume      : 15
% 4.55/1.84  #Demod        : 309
% 4.55/1.84  #Tautology    : 168
% 4.55/1.84  #SimpNegUnit  : 2
% 4.55/1.84  #BackRed      : 1
% 4.55/1.84  
% 4.55/1.84  #Partial instantiations: 0
% 4.55/1.84  #Strategies tried      : 1
% 4.55/1.84  
% 4.55/1.84  Timing (in seconds)
% 4.55/1.84  ----------------------
% 4.55/1.85  Preprocessing        : 0.30
% 4.55/1.85  Parsing              : 0.16
% 4.55/1.85  CNF conversion       : 0.02
% 4.55/1.85  Main loop            : 0.78
% 4.55/1.85  Inferencing          : 0.24
% 4.55/1.85  Reduction            : 0.30
% 4.55/1.85  Demodulation         : 0.23
% 4.55/1.85  BG Simplification    : 0.04
% 4.55/1.85  Subsumption          : 0.14
% 4.55/1.85  Abstraction          : 0.06
% 4.55/1.85  MUC search           : 0.00
% 4.55/1.85  Cooper               : 0.00
% 4.55/1.85  Total                : 1.11
% 4.55/1.85  Index Insertion      : 0.00
% 4.55/1.85  Index Deletion       : 0.00
% 4.55/1.85  Index Matching       : 0.00
% 4.55/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
