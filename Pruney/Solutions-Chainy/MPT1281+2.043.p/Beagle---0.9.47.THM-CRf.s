%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:19 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 144 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 315 expanded)
%              Number of equality atoms :   17 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
           => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_87,plain,(
    ! [A_47,B_48] :
      ( k2_pre_topc(A_47,k1_tops_1(A_47,B_48)) = B_48
      | ~ v5_tops_1(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_87])).

tff(c_98,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_93])).

tff(c_20,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_99,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_20])).

tff(c_177,plain,(
    ! [A_58,B_59] :
      ( k2_tops_1(A_58,k1_tops_1(A_58,B_59)) = k2_tops_1(A_58,B_59)
      | ~ v5_tops_1(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_183,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_177])).

tff(c_188,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_183])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k1_tops_1(A_12,B_13),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k2_tops_1(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_192,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_14])).

tff(c_196,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_192])).

tff(c_198,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_201,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_198])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_201])).

tff(c_207,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_18,plain,(
    ! [A_19,B_21] :
      ( k4_subset_1(u1_struct_0(A_19),B_21,k2_tops_1(A_19,B_21)) = k2_pre_topc(A_19,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_248,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_207,c_18])).

tff(c_264,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_98,c_188,c_248])).

tff(c_206,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( k4_subset_1(A_6,B_7,C_8) = k2_xboole_0(B_7,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_315,plain,(
    ! [B_62] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_62,k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(B_62,k2_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_206,c_6])).

tff(c_318,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_207,c_315])).

tff(c_334,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_318])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_tarski(A_25,k2_xboole_0(B_26,C_27))
      | ~ r1_tarski(k4_xboole_0(A_25,B_26),C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(resolution,[status(thm)],[c_2,c_28])).

tff(c_347,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_32])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.30  
% 2.45/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.31  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.45/1.31  
% 2.45/1.31  %Foreground sorts:
% 2.45/1.31  
% 2.45/1.31  
% 2.45/1.31  %Background operators:
% 2.45/1.31  
% 2.45/1.31  
% 2.45/1.31  %Foreground operators:
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.31  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.45/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.45/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.45/1.31  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.45/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.31  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.45/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.45/1.31  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.45/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.31  
% 2.45/1.32  tff(f_84, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 2.45/1.32  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 2.45/1.32  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 2.45/1.32  tff(f_52, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.45/1.32  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.45/1.32  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 2.45/1.32  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.45/1.32  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.45/1.32  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.45/1.32  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.45/1.32  tff(c_22, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.45/1.32  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.45/1.32  tff(c_87, plain, (![A_47, B_48]: (k2_pre_topc(A_47, k1_tops_1(A_47, B_48))=B_48 | ~v5_tops_1(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.45/1.32  tff(c_93, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_87])).
% 2.45/1.32  tff(c_98, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_93])).
% 2.45/1.32  tff(c_20, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.45/1.32  tff(c_99, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_20])).
% 2.45/1.32  tff(c_177, plain, (![A_58, B_59]: (k2_tops_1(A_58, k1_tops_1(A_58, B_59))=k2_tops_1(A_58, B_59) | ~v5_tops_1(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.45/1.32  tff(c_183, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_177])).
% 2.45/1.32  tff(c_188, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_183])).
% 2.45/1.32  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(k1_tops_1(A_12, B_13), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.45/1.32  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(k2_tops_1(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.45/1.32  tff(c_192, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_188, c_14])).
% 2.45/1.32  tff(c_196, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_192])).
% 2.45/1.32  tff(c_198, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_196])).
% 2.45/1.32  tff(c_201, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_198])).
% 2.45/1.32  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_201])).
% 2.45/1.32  tff(c_207, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_196])).
% 2.45/1.32  tff(c_18, plain, (![A_19, B_21]: (k4_subset_1(u1_struct_0(A_19), B_21, k2_tops_1(A_19, B_21))=k2_pre_topc(A_19, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.45/1.32  tff(c_248, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_207, c_18])).
% 2.45/1.32  tff(c_264, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_98, c_188, c_248])).
% 2.45/1.32  tff(c_206, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_196])).
% 2.45/1.32  tff(c_6, plain, (![A_6, B_7, C_8]: (k4_subset_1(A_6, B_7, C_8)=k2_xboole_0(B_7, C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.32  tff(c_315, plain, (![B_62]: (k4_subset_1(u1_struct_0('#skF_1'), B_62, k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(B_62, k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_206, c_6])).
% 2.45/1.32  tff(c_318, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_207, c_315])).
% 2.45/1.32  tff(c_334, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_264, c_318])).
% 2.45/1.32  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.32  tff(c_28, plain, (![A_25, B_26, C_27]: (r1_tarski(A_25, k2_xboole_0(B_26, C_27)) | ~r1_tarski(k4_xboole_0(A_25, B_26), C_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.32  tff(c_32, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(resolution, [status(thm)], [c_2, c_28])).
% 2.45/1.32  tff(c_347, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_334, c_32])).
% 2.45/1.32  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_347])).
% 2.45/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.32  
% 2.45/1.32  Inference rules
% 2.45/1.32  ----------------------
% 2.45/1.32  #Ref     : 0
% 2.45/1.32  #Sup     : 78
% 2.45/1.32  #Fact    : 0
% 2.45/1.32  #Define  : 0
% 2.45/1.32  #Split   : 3
% 2.45/1.32  #Chain   : 0
% 2.45/1.32  #Close   : 0
% 2.45/1.32  
% 2.45/1.32  Ordering : KBO
% 2.45/1.32  
% 2.45/1.32  Simplification rules
% 2.45/1.32  ----------------------
% 2.45/1.32  #Subsume      : 2
% 2.45/1.32  #Demod        : 39
% 2.45/1.32  #Tautology    : 27
% 2.45/1.32  #SimpNegUnit  : 1
% 2.45/1.32  #BackRed      : 1
% 2.45/1.32  
% 2.45/1.32  #Partial instantiations: 0
% 2.45/1.32  #Strategies tried      : 1
% 2.45/1.32  
% 2.45/1.32  Timing (in seconds)
% 2.45/1.32  ----------------------
% 2.45/1.32  Preprocessing        : 0.31
% 2.45/1.32  Parsing              : 0.17
% 2.45/1.32  CNF conversion       : 0.02
% 2.45/1.32  Main loop            : 0.25
% 2.45/1.33  Inferencing          : 0.09
% 2.45/1.33  Reduction            : 0.08
% 2.45/1.33  Demodulation         : 0.06
% 2.45/1.33  BG Simplification    : 0.02
% 2.45/1.33  Subsumption          : 0.05
% 2.45/1.33  Abstraction          : 0.02
% 2.45/1.33  MUC search           : 0.00
% 2.45/1.33  Cooper               : 0.00
% 2.45/1.33  Total                : 0.60
% 2.45/1.33  Index Insertion      : 0.00
% 2.45/1.33  Index Deletion       : 0.00
% 2.45/1.33  Index Matching       : 0.00
% 2.45/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
