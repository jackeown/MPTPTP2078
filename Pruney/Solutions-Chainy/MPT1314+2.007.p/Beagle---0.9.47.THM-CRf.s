%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:00 EST 2020

% Result     : Theorem 8.92s
% Output     : CNFRefutation 8.92s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 281 expanded)
%              Number of leaves         :   30 ( 111 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 678 expanded)
%              Number of equality atoms :   21 ( 123 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v3_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v3_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).

tff(c_32,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    ~ v3_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_99,plain,(
    ! [B_60,A_61] :
      ( l1_pre_topc(B_60)
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_102,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_99])).

tff(c_105,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_18,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    ! [A_16] :
      ( u1_struct_0(A_16) = k2_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_83])).

tff(c_110,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_87])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_43,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_111,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_43])).

tff(c_116,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_111,c_116])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_126,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_18,c_83])).

tff(c_92,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_88])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_93,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_40])).

tff(c_128,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_93,c_116])).

tff(c_36,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_160,plain,(
    ! [A_68,B_69,C_70] :
      ( k9_subset_1(A_68,B_69,C_70) = k3_xboole_0(B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_167,plain,(
    ! [B_69] : k9_subset_1(k2_struct_0('#skF_4'),B_69,'#skF_3') = k3_xboole_0(B_69,'#skF_3') ),
    inference(resolution,[status(thm)],[c_111,c_160])).

tff(c_197,plain,(
    ! [A_76,C_77,B_78] :
      ( k9_subset_1(A_76,C_77,B_78) = k9_subset_1(A_76,B_78,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_199,plain,(
    ! [B_78] : k9_subset_1(k2_struct_0('#skF_4'),B_78,'#skF_3') = k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',B_78) ),
    inference(resolution,[status(thm)],[c_111,c_197])).

tff(c_205,plain,(
    ! [B_78] : k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',B_78) = k3_xboole_0(B_78,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_199])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_941,plain,(
    ! [B_118,D_119,A_120] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_118),D_119,k2_struct_0(B_118)),B_118)
      | ~ v3_pre_topc(D_119,A_120)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_118),D_119,k2_struct_0(B_118)),k1_zfmisc_1(u1_struct_0(B_118)))
      | ~ m1_pre_topc(B_118,A_120)
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2364,plain,(
    ! [B_167,A_168,A_169] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_167),A_168,k2_struct_0(B_167)),B_167)
      | ~ v3_pre_topc(A_168,A_169)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_167),A_168,k2_struct_0(B_167)),k1_zfmisc_1(u1_struct_0(B_167)))
      | ~ m1_pre_topc(B_167,A_169)
      | ~ l1_pre_topc(A_169)
      | ~ r1_tarski(A_168,u1_struct_0(A_169)) ) ),
    inference(resolution,[status(thm)],[c_14,c_941])).

tff(c_6073,plain,(
    ! [B_233,A_234,A_235] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_233),A_234,k2_struct_0(B_233)),B_233)
      | ~ v3_pre_topc(A_234,A_235)
      | ~ m1_pre_topc(B_233,A_235)
      | ~ l1_pre_topc(A_235)
      | ~ r1_tarski(A_234,u1_struct_0(A_235))
      | ~ r1_tarski(k9_subset_1(u1_struct_0(B_233),A_234,k2_struct_0(B_233)),u1_struct_0(B_233)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2364])).

tff(c_6075,plain,(
    ! [A_234] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),A_234,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(A_234,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_234,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),A_234,k2_struct_0('#skF_4')),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_6073])).

tff(c_6607,plain,(
    ! [A_240] :
      ( v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'),A_240,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(A_240,'#skF_2')
      | ~ r1_tarski(A_240,k2_struct_0('#skF_2'))
      | ~ r1_tarski(k9_subset_1(k2_struct_0('#skF_4'),A_240,k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_92,c_42,c_110,c_6075])).

tff(c_6611,plain,
    ( v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',k2_struct_0('#skF_4')),'#skF_4')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2'))
    | ~ r1_tarski(k3_xboole_0(k2_struct_0('#skF_4'),'#skF_3'),k2_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_6607])).

tff(c_6613,plain,(
    v3_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_132,c_2,c_128,c_36,c_132,c_2,c_205,c_6611])).

tff(c_6615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_6613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:19:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.92/3.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.92/3.47  
% 8.92/3.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.92/3.47  %$ v3_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 8.92/3.47  
% 8.92/3.47  %Foreground sorts:
% 8.92/3.47  
% 8.92/3.47  
% 8.92/3.47  %Background operators:
% 8.92/3.47  
% 8.92/3.47  
% 8.92/3.47  %Foreground operators:
% 8.92/3.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.92/3.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.92/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.92/3.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.92/3.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.92/3.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.92/3.47  tff('#skF_5', type, '#skF_5': $i).
% 8.92/3.47  tff('#skF_2', type, '#skF_2': $i).
% 8.92/3.47  tff('#skF_3', type, '#skF_3': $i).
% 8.92/3.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.92/3.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.92/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.92/3.47  tff('#skF_4', type, '#skF_4': $i).
% 8.92/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.92/3.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.92/3.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.92/3.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.92/3.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.92/3.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.92/3.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.92/3.47  
% 8.92/3.48  tff(f_95, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 8.92/3.48  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.92/3.48  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.92/3.48  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 8.92/3.48  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.92/3.48  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.92/3.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.92/3.48  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.92/3.48  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 8.92/3.48  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_2)).
% 8.92/3.48  tff(c_32, plain, ('#skF_5'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.92/3.48  tff(c_30, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.92/3.48  tff(c_44, plain, (~v3_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30])).
% 8.92/3.48  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.92/3.48  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.92/3.48  tff(c_99, plain, (![B_60, A_61]: (l1_pre_topc(B_60) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.92/3.48  tff(c_102, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_99])).
% 8.92/3.48  tff(c_105, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_102])).
% 8.92/3.48  tff(c_18, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.92/3.48  tff(c_83, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.92/3.48  tff(c_87, plain, (![A_16]: (u1_struct_0(A_16)=k2_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_18, c_83])).
% 8.92/3.48  tff(c_110, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_105, c_87])).
% 8.92/3.48  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.92/3.48  tff(c_43, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 8.92/3.48  tff(c_111, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_43])).
% 8.92/3.48  tff(c_116, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.92/3.48  tff(c_126, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_111, c_116])).
% 8.92/3.48  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.92/3.48  tff(c_132, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_126, c_4])).
% 8.92/3.48  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.92/3.48  tff(c_88, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_18, c_83])).
% 8.92/3.48  tff(c_92, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_88])).
% 8.92/3.48  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.92/3.48  tff(c_93, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_40])).
% 8.92/3.48  tff(c_128, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_93, c_116])).
% 8.92/3.48  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.92/3.48  tff(c_160, plain, (![A_68, B_69, C_70]: (k9_subset_1(A_68, B_69, C_70)=k3_xboole_0(B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.92/3.48  tff(c_167, plain, (![B_69]: (k9_subset_1(k2_struct_0('#skF_4'), B_69, '#skF_3')=k3_xboole_0(B_69, '#skF_3'))), inference(resolution, [status(thm)], [c_111, c_160])).
% 8.92/3.48  tff(c_197, plain, (![A_76, C_77, B_78]: (k9_subset_1(A_76, C_77, B_78)=k9_subset_1(A_76, B_78, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.92/3.48  tff(c_199, plain, (![B_78]: (k9_subset_1(k2_struct_0('#skF_4'), B_78, '#skF_3')=k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', B_78))), inference(resolution, [status(thm)], [c_111, c_197])).
% 8.92/3.48  tff(c_205, plain, (![B_78]: (k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', B_78)=k3_xboole_0(B_78, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_199])).
% 8.92/3.48  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.92/3.48  tff(c_941, plain, (![B_118, D_119, A_120]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_118), D_119, k2_struct_0(B_118)), B_118) | ~v3_pre_topc(D_119, A_120) | ~m1_subset_1(D_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_118), D_119, k2_struct_0(B_118)), k1_zfmisc_1(u1_struct_0(B_118))) | ~m1_pre_topc(B_118, A_120) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.92/3.48  tff(c_2364, plain, (![B_167, A_168, A_169]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_167), A_168, k2_struct_0(B_167)), B_167) | ~v3_pre_topc(A_168, A_169) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_167), A_168, k2_struct_0(B_167)), k1_zfmisc_1(u1_struct_0(B_167))) | ~m1_pre_topc(B_167, A_169) | ~l1_pre_topc(A_169) | ~r1_tarski(A_168, u1_struct_0(A_169)))), inference(resolution, [status(thm)], [c_14, c_941])).
% 8.92/3.48  tff(c_6073, plain, (![B_233, A_234, A_235]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_233), A_234, k2_struct_0(B_233)), B_233) | ~v3_pre_topc(A_234, A_235) | ~m1_pre_topc(B_233, A_235) | ~l1_pre_topc(A_235) | ~r1_tarski(A_234, u1_struct_0(A_235)) | ~r1_tarski(k9_subset_1(u1_struct_0(B_233), A_234, k2_struct_0(B_233)), u1_struct_0(B_233)))), inference(resolution, [status(thm)], [c_14, c_2364])).
% 8.92/3.48  tff(c_6075, plain, (![A_234]: (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'), A_234, k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc(A_234, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_234, u1_struct_0('#skF_2')) | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), A_234, k2_struct_0('#skF_4')), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_38, c_6073])).
% 8.92/3.48  tff(c_6607, plain, (![A_240]: (v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'), A_240, k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc(A_240, '#skF_2') | ~r1_tarski(A_240, k2_struct_0('#skF_2')) | ~r1_tarski(k9_subset_1(k2_struct_0('#skF_4'), A_240, k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_92, c_42, c_110, c_6075])).
% 8.92/3.48  tff(c_6611, plain, (v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2')) | ~r1_tarski(k3_xboole_0(k2_struct_0('#skF_4'), '#skF_3'), k2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_205, c_6607])).
% 8.92/3.48  tff(c_6613, plain, (v3_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_132, c_2, c_128, c_36, c_132, c_2, c_205, c_6611])).
% 8.92/3.48  tff(c_6615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_6613])).
% 8.92/3.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.92/3.48  
% 8.92/3.48  Inference rules
% 8.92/3.48  ----------------------
% 8.92/3.48  #Ref     : 0
% 8.92/3.48  #Sup     : 1685
% 8.92/3.48  #Fact    : 0
% 8.92/3.48  #Define  : 0
% 8.92/3.48  #Split   : 2
% 8.92/3.48  #Chain   : 0
% 8.92/3.48  #Close   : 0
% 8.92/3.48  
% 8.92/3.48  Ordering : KBO
% 8.92/3.48  
% 8.92/3.48  Simplification rules
% 8.92/3.48  ----------------------
% 8.92/3.48  #Subsume      : 129
% 8.92/3.48  #Demod        : 2894
% 8.92/3.48  #Tautology    : 646
% 8.92/3.48  #SimpNegUnit  : 1
% 8.92/3.48  #BackRed      : 2
% 8.92/3.48  
% 8.92/3.48  #Partial instantiations: 0
% 8.92/3.48  #Strategies tried      : 1
% 8.92/3.48  
% 8.92/3.48  Timing (in seconds)
% 8.92/3.48  ----------------------
% 8.92/3.49  Preprocessing        : 0.31
% 8.92/3.49  Parsing              : 0.16
% 8.92/3.49  CNF conversion       : 0.02
% 8.92/3.49  Main loop            : 2.41
% 8.92/3.49  Inferencing          : 0.48
% 8.92/3.49  Reduction            : 1.58
% 8.92/3.49  Demodulation         : 1.46
% 8.92/3.49  BG Simplification    : 0.07
% 8.92/3.49  Subsumption          : 0.21
% 8.92/3.49  Abstraction          : 0.13
% 8.92/3.49  MUC search           : 0.00
% 8.92/3.49  Cooper               : 0.00
% 8.92/3.49  Total                : 2.75
% 8.92/3.49  Index Insertion      : 0.00
% 8.92/3.49  Index Deletion       : 0.00
% 8.92/3.49  Index Matching       : 0.00
% 8.92/3.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
