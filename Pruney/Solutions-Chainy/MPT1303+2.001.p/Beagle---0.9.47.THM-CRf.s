%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:46 EST 2020

% Result     : Theorem 8.09s
% Output     : CNFRefutation 8.09s
% Verified   : 
% Statistics : Number of formulae       :   57 (  85 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 139 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_72,negated_conjecture,(
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
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
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

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_130,plain,(
    ! [A_39,B_40,C_41] :
      ( k9_subset_1(A_39,B_40,C_41) = k3_xboole_0(B_40,C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_140,plain,(
    ! [B_40] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_40,'#skF_2') = k3_xboole_0(B_40,'#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_130])).

tff(c_219,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1(k9_subset_1(A_51,B_52,C_53),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_227,plain,(
    ! [B_40] :
      ( m1_subset_1(k3_xboole_0(B_40,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_219])).

tff(c_237,plain,(
    ! [B_40] : m1_subset_1(k3_xboole_0(B_40,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_227])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_142,plain,(
    ! [A_4,B_40] : k9_subset_1(A_4,B_40,A_4) = k3_xboole_0(B_40,A_4) ),
    inference(resolution,[status(thm)],[c_29,c_130])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_356,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(k9_subset_1(A_68,B_69,C_70),A_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_219,c_14])).

tff(c_18,plain,(
    ! [B_19,A_15,C_21] :
      ( v1_tops_2(B_19,A_15)
      | ~ v1_tops_2(C_21,A_15)
      | ~ r1_tarski(B_19,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15))))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15))))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1304,plain,(
    ! [A_142,B_143,C_144,A_145] :
      ( v1_tops_2(k9_subset_1(A_142,B_143,C_144),A_145)
      | ~ v1_tops_2(A_142,A_145)
      | ~ m1_subset_1(A_142,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145))))
      | ~ m1_subset_1(k9_subset_1(A_142,B_143,C_144),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145))))
      | ~ l1_pre_topc(A_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(A_142)) ) ),
    inference(resolution,[status(thm)],[c_356,c_18])).

tff(c_1338,plain,(
    ! [A_4,B_40,A_145] :
      ( v1_tops_2(k9_subset_1(A_4,B_40,A_4),A_145)
      | ~ v1_tops_2(A_4,A_145)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145))))
      | ~ m1_subset_1(k3_xboole_0(B_40,A_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145))))
      | ~ l1_pre_topc(A_145)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_1304])).

tff(c_10043,plain,(
    ! [B_312,A_313,A_314] :
      ( v1_tops_2(k3_xboole_0(B_312,A_313),A_314)
      | ~ v1_tops_2(A_313,A_314)
      | ~ m1_subset_1(A_313,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_314))))
      | ~ m1_subset_1(k3_xboole_0(B_312,A_313),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_314))))
      | ~ l1_pre_topc(A_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_142,c_1338])).

tff(c_10167,plain,(
    ! [B_40] :
      ( v1_tops_2(k3_xboole_0(B_40,'#skF_2'),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_237,c_10043])).

tff(c_10251,plain,(
    ! [B_40] : v1_tops_2(k3_xboole_0(B_40,'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_10167])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(B_38,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_74])).

tff(c_12,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    ! [B_38,A_37] : k3_xboole_0(B_38,A_37) = k3_xboole_0(A_37,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_12])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_141,plain,(
    ! [B_40] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_40,'#skF_3') = k3_xboole_0(B_40,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_130])).

tff(c_20,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_185,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_20])).

tff(c_186,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_185])).

tff(c_10259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10251,c_186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:14:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.09/2.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.09/2.96  
% 8.09/2.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.09/2.96  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 8.09/2.96  
% 8.09/2.96  %Foreground sorts:
% 8.09/2.96  
% 8.09/2.96  
% 8.09/2.96  %Background operators:
% 8.09/2.96  
% 8.09/2.96  
% 8.09/2.96  %Foreground operators:
% 8.09/2.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.09/2.96  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 8.09/2.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.09/2.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.09/2.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.09/2.96  tff('#skF_2', type, '#skF_2': $i).
% 8.09/2.96  tff('#skF_3', type, '#skF_3': $i).
% 8.09/2.96  tff('#skF_1', type, '#skF_1': $i).
% 8.09/2.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.09/2.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.09/2.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.09/2.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.09/2.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.09/2.96  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.09/2.96  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.09/2.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.09/2.96  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.09/2.96  
% 8.09/2.98  tff(f_72, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_tops_2)).
% 8.09/2.98  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.09/2.98  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 8.09/2.98  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.09/2.98  tff(f_31, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.09/2.98  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.09/2.98  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 8.09/2.98  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.09/2.98  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.09/2.98  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.09/2.98  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.09/2.98  tff(c_22, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.09/2.98  tff(c_130, plain, (![A_39, B_40, C_41]: (k9_subset_1(A_39, B_40, C_41)=k3_xboole_0(B_40, C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.09/2.98  tff(c_140, plain, (![B_40]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_40, '#skF_2')=k3_xboole_0(B_40, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_130])).
% 8.09/2.98  tff(c_219, plain, (![A_51, B_52, C_53]: (m1_subset_1(k9_subset_1(A_51, B_52, C_53), k1_zfmisc_1(A_51)) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.09/2.98  tff(c_227, plain, (![B_40]: (m1_subset_1(k3_xboole_0(B_40, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_140, c_219])).
% 8.09/2.98  tff(c_237, plain, (![B_40]: (m1_subset_1(k3_xboole_0(B_40, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_227])).
% 8.09/2.98  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.09/2.98  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.09/2.98  tff(c_29, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 8.09/2.98  tff(c_142, plain, (![A_4, B_40]: (k9_subset_1(A_4, B_40, A_4)=k3_xboole_0(B_40, A_4))), inference(resolution, [status(thm)], [c_29, c_130])).
% 8.09/2.98  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.09/2.98  tff(c_356, plain, (![A_68, B_69, C_70]: (r1_tarski(k9_subset_1(A_68, B_69, C_70), A_68) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_219, c_14])).
% 8.09/2.98  tff(c_18, plain, (![B_19, A_15, C_21]: (v1_tops_2(B_19, A_15) | ~v1_tops_2(C_21, A_15) | ~r1_tarski(B_19, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15)))) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15)))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.09/2.98  tff(c_1304, plain, (![A_142, B_143, C_144, A_145]: (v1_tops_2(k9_subset_1(A_142, B_143, C_144), A_145) | ~v1_tops_2(A_142, A_145) | ~m1_subset_1(A_142, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145)))) | ~m1_subset_1(k9_subset_1(A_142, B_143, C_144), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145)))) | ~l1_pre_topc(A_145) | ~m1_subset_1(C_144, k1_zfmisc_1(A_142)))), inference(resolution, [status(thm)], [c_356, c_18])).
% 8.09/2.98  tff(c_1338, plain, (![A_4, B_40, A_145]: (v1_tops_2(k9_subset_1(A_4, B_40, A_4), A_145) | ~v1_tops_2(A_4, A_145) | ~m1_subset_1(A_4, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145)))) | ~m1_subset_1(k3_xboole_0(B_40, A_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145)))) | ~l1_pre_topc(A_145) | ~m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_1304])).
% 8.09/2.98  tff(c_10043, plain, (![B_312, A_313, A_314]: (v1_tops_2(k3_xboole_0(B_312, A_313), A_314) | ~v1_tops_2(A_313, A_314) | ~m1_subset_1(A_313, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_314)))) | ~m1_subset_1(k3_xboole_0(B_312, A_313), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_314)))) | ~l1_pre_topc(A_314))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_142, c_1338])).
% 8.09/2.98  tff(c_10167, plain, (![B_40]: (v1_tops_2(k3_xboole_0(B_40, '#skF_2'), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_237, c_10043])).
% 8.09/2.98  tff(c_10251, plain, (![B_40]: (v1_tops_2(k3_xboole_0(B_40, '#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_10167])).
% 8.09/2.98  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.09/2.98  tff(c_74, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.09/2.98  tff(c_107, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(B_38, A_37))), inference(superposition, [status(thm), theory('equality')], [c_2, c_74])).
% 8.09/2.98  tff(c_12, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.09/2.98  tff(c_113, plain, (![B_38, A_37]: (k3_xboole_0(B_38, A_37)=k3_xboole_0(A_37, B_38))), inference(superposition, [status(thm), theory('equality')], [c_107, c_12])).
% 8.09/2.98  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.09/2.98  tff(c_141, plain, (![B_40]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_40, '#skF_3')=k3_xboole_0(B_40, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_130])).
% 8.09/2.98  tff(c_20, plain, (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.09/2.98  tff(c_185, plain, (~v1_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_20])).
% 8.09/2.98  tff(c_186, plain, (~v1_tops_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_185])).
% 8.09/2.98  tff(c_10259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10251, c_186])).
% 8.09/2.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.09/2.98  
% 8.09/2.98  Inference rules
% 8.09/2.98  ----------------------
% 8.09/2.98  #Ref     : 0
% 8.09/2.98  #Sup     : 2428
% 8.09/2.98  #Fact    : 0
% 8.09/2.98  #Define  : 0
% 8.09/2.98  #Split   : 1
% 8.09/2.98  #Chain   : 0
% 8.09/2.98  #Close   : 0
% 8.09/2.98  
% 8.09/2.98  Ordering : KBO
% 8.09/2.98  
% 8.09/2.98  Simplification rules
% 8.09/2.98  ----------------------
% 8.09/2.98  #Subsume      : 77
% 8.09/2.98  #Demod        : 1573
% 8.09/2.98  #Tautology    : 1272
% 8.09/2.98  #SimpNegUnit  : 0
% 8.09/2.98  #BackRed      : 2
% 8.09/2.98  
% 8.09/2.98  #Partial instantiations: 0
% 8.09/2.98  #Strategies tried      : 1
% 8.09/2.98  
% 8.09/2.98  Timing (in seconds)
% 8.09/2.98  ----------------------
% 8.09/2.98  Preprocessing        : 0.32
% 8.09/2.98  Parsing              : 0.18
% 8.09/2.98  CNF conversion       : 0.02
% 8.09/2.98  Main loop            : 1.86
% 8.09/2.98  Inferencing          : 0.43
% 8.09/2.98  Reduction            : 1.05
% 8.09/2.98  Demodulation         : 0.94
% 8.09/2.98  BG Simplification    : 0.06
% 8.09/2.98  Subsumption          : 0.23
% 8.09/2.98  Abstraction          : 0.08
% 8.09/2.98  MUC search           : 0.00
% 8.09/2.98  Cooper               : 0.00
% 8.09/2.98  Total                : 2.21
% 8.09/2.98  Index Insertion      : 0.00
% 8.09/2.98  Index Deletion       : 0.00
% 8.09/2.98  Index Matching       : 0.00
% 8.09/2.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
