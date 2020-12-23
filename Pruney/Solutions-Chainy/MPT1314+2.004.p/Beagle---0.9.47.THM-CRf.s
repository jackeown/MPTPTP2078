%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:59 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 294 expanded)
%              Number of leaves         :   32 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 690 expanded)
%              Number of equality atoms :   26 ( 135 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
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

tff(c_112,plain,(
    ! [B_62,A_63] :
      ( l1_pre_topc(B_62)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_112])).

tff(c_118,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_115])).

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

tff(c_122,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_87])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_43,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_99,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_43,c_99])).

tff(c_123,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_111])).

tff(c_149,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_123,c_149])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_64,B_65] : k1_setfam_1(k2_tarski(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_176,plain,(
    ! [A_71,B_72] : k1_setfam_1(k2_tarski(A_71,B_72)) = k3_xboole_0(B_72,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_134])).

tff(c_10,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [B_72,A_71] : k3_xboole_0(B_72,A_71) = k3_xboole_0(A_71,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_10])).

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

tff(c_110,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_93,c_99])).

tff(c_36,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_124,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_43])).

tff(c_162,plain,(
    ! [A_68,B_69,C_70] :
      ( k9_subset_1(A_68,B_69,C_70) = k3_xboole_0(B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_169,plain,(
    ! [B_69] : k9_subset_1(k2_struct_0('#skF_4'),B_69,'#skF_3') = k3_xboole_0(B_69,'#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_162])).

tff(c_260,plain,(
    ! [A_80,C_81,B_82] :
      ( k9_subset_1(A_80,C_81,B_82) = k9_subset_1(A_80,B_82,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_262,plain,(
    ! [B_82] : k9_subset_1(k2_struct_0('#skF_4'),B_82,'#skF_3') = k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',B_82) ),
    inference(resolution,[status(thm)],[c_124,c_260])).

tff(c_268,plain,(
    ! [B_82] : k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',B_82) = k3_xboole_0(B_82,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_262])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_604,plain,(
    ! [B_132,D_133,A_134] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_132),D_133,k2_struct_0(B_132)),B_132)
      | ~ v3_pre_topc(D_133,A_134)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_132),D_133,k2_struct_0(B_132)),k1_zfmisc_1(u1_struct_0(B_132)))
      | ~ m1_pre_topc(B_132,A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_973,plain,(
    ! [B_174,A_175,A_176] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_174),A_175,k2_struct_0(B_174)),B_174)
      | ~ v3_pre_topc(A_175,A_176)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_174),A_175,k2_struct_0(B_174)),k1_zfmisc_1(u1_struct_0(B_174)))
      | ~ m1_pre_topc(B_174,A_176)
      | ~ l1_pre_topc(A_176)
      | ~ r1_tarski(A_175,u1_struct_0(A_176)) ) ),
    inference(resolution,[status(thm)],[c_14,c_604])).

tff(c_2250,plain,(
    ! [B_250,A_251,A_252] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_250),A_251,k2_struct_0(B_250)),B_250)
      | ~ v3_pre_topc(A_251,A_252)
      | ~ m1_pre_topc(B_250,A_252)
      | ~ l1_pre_topc(A_252)
      | ~ r1_tarski(A_251,u1_struct_0(A_252))
      | ~ r1_tarski(k9_subset_1(u1_struct_0(B_250),A_251,k2_struct_0(B_250)),u1_struct_0(B_250)) ) ),
    inference(resolution,[status(thm)],[c_14,c_973])).

tff(c_2252,plain,(
    ! [A_251] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),A_251,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(A_251,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_251,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),A_251,k2_struct_0('#skF_4')),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_2250])).

tff(c_2256,plain,(
    ! [A_253] :
      ( v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'),A_253,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(A_253,'#skF_2')
      | ~ r1_tarski(A_253,k2_struct_0('#skF_2'))
      | ~ r1_tarski(k9_subset_1(k2_struct_0('#skF_4'),A_253,k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_122,c_92,c_42,c_122,c_2252])).

tff(c_2267,plain,
    ( v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',k2_struct_0('#skF_4')),'#skF_4')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2'))
    | ~ r1_tarski(k3_xboole_0(k2_struct_0('#skF_4'),'#skF_3'),k2_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_2256])).

tff(c_2269,plain,(
    v3_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_156,c_182,c_110,c_36,c_156,c_182,c_268,c_2267])).

tff(c_2271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:34:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.81  
% 4.63/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.82  %$ v3_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.63/1.82  
% 4.63/1.82  %Foreground sorts:
% 4.63/1.82  
% 4.63/1.82  
% 4.63/1.82  %Background operators:
% 4.63/1.82  
% 4.63/1.82  
% 4.63/1.82  %Foreground operators:
% 4.63/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.63/1.82  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.63/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.63/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.63/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.82  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.63/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.82  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.63/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.63/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.63/1.82  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.63/1.82  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.63/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.63/1.82  
% 4.67/1.83  tff(f_95, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 4.67/1.83  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.67/1.83  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.67/1.83  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.67/1.83  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.67/1.83  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.67/1.83  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.67/1.83  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.67/1.83  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.67/1.83  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.67/1.83  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_2)).
% 4.67/1.83  tff(c_32, plain, ('#skF_5'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.83  tff(c_30, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.83  tff(c_44, plain, (~v3_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30])).
% 4.67/1.83  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.83  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.83  tff(c_112, plain, (![B_62, A_63]: (l1_pre_topc(B_62) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.67/1.83  tff(c_115, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_112])).
% 4.67/1.83  tff(c_118, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_115])).
% 4.67/1.83  tff(c_18, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.67/1.83  tff(c_83, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.67/1.83  tff(c_87, plain, (![A_16]: (u1_struct_0(A_16)=k2_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_18, c_83])).
% 4.67/1.83  tff(c_122, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_118, c_87])).
% 4.67/1.83  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.83  tff(c_43, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 4.67/1.83  tff(c_99, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.67/1.83  tff(c_111, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_43, c_99])).
% 4.67/1.83  tff(c_123, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_111])).
% 4.67/1.83  tff(c_149, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.67/1.83  tff(c_156, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_123, c_149])).
% 4.67/1.83  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.67/1.83  tff(c_134, plain, (![A_64, B_65]: (k1_setfam_1(k2_tarski(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.67/1.83  tff(c_176, plain, (![A_71, B_72]: (k1_setfam_1(k2_tarski(A_71, B_72))=k3_xboole_0(B_72, A_71))), inference(superposition, [status(thm), theory('equality')], [c_4, c_134])).
% 4.67/1.83  tff(c_10, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.67/1.83  tff(c_182, plain, (![B_72, A_71]: (k3_xboole_0(B_72, A_71)=k3_xboole_0(A_71, B_72))), inference(superposition, [status(thm), theory('equality')], [c_176, c_10])).
% 4.67/1.83  tff(c_88, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_18, c_83])).
% 4.67/1.83  tff(c_92, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_88])).
% 4.67/1.83  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.83  tff(c_93, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_40])).
% 4.67/1.83  tff(c_110, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_93, c_99])).
% 4.67/1.83  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.83  tff(c_124, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_43])).
% 4.67/1.83  tff(c_162, plain, (![A_68, B_69, C_70]: (k9_subset_1(A_68, B_69, C_70)=k3_xboole_0(B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.67/1.83  tff(c_169, plain, (![B_69]: (k9_subset_1(k2_struct_0('#skF_4'), B_69, '#skF_3')=k3_xboole_0(B_69, '#skF_3'))), inference(resolution, [status(thm)], [c_124, c_162])).
% 4.67/1.83  tff(c_260, plain, (![A_80, C_81, B_82]: (k9_subset_1(A_80, C_81, B_82)=k9_subset_1(A_80, B_82, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.67/1.83  tff(c_262, plain, (![B_82]: (k9_subset_1(k2_struct_0('#skF_4'), B_82, '#skF_3')=k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', B_82))), inference(resolution, [status(thm)], [c_124, c_260])).
% 4.67/1.83  tff(c_268, plain, (![B_82]: (k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', B_82)=k3_xboole_0(B_82, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_262])).
% 4.67/1.83  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.67/1.83  tff(c_604, plain, (![B_132, D_133, A_134]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_132), D_133, k2_struct_0(B_132)), B_132) | ~v3_pre_topc(D_133, A_134) | ~m1_subset_1(D_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_132), D_133, k2_struct_0(B_132)), k1_zfmisc_1(u1_struct_0(B_132))) | ~m1_pre_topc(B_132, A_134) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.67/1.83  tff(c_973, plain, (![B_174, A_175, A_176]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_174), A_175, k2_struct_0(B_174)), B_174) | ~v3_pre_topc(A_175, A_176) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_174), A_175, k2_struct_0(B_174)), k1_zfmisc_1(u1_struct_0(B_174))) | ~m1_pre_topc(B_174, A_176) | ~l1_pre_topc(A_176) | ~r1_tarski(A_175, u1_struct_0(A_176)))), inference(resolution, [status(thm)], [c_14, c_604])).
% 4.67/1.83  tff(c_2250, plain, (![B_250, A_251, A_252]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_250), A_251, k2_struct_0(B_250)), B_250) | ~v3_pre_topc(A_251, A_252) | ~m1_pre_topc(B_250, A_252) | ~l1_pre_topc(A_252) | ~r1_tarski(A_251, u1_struct_0(A_252)) | ~r1_tarski(k9_subset_1(u1_struct_0(B_250), A_251, k2_struct_0(B_250)), u1_struct_0(B_250)))), inference(resolution, [status(thm)], [c_14, c_973])).
% 4.67/1.83  tff(c_2252, plain, (![A_251]: (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'), A_251, k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc(A_251, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_251, u1_struct_0('#skF_2')) | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), A_251, k2_struct_0('#skF_4')), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_38, c_2250])).
% 4.67/1.83  tff(c_2256, plain, (![A_253]: (v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'), A_253, k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc(A_253, '#skF_2') | ~r1_tarski(A_253, k2_struct_0('#skF_2')) | ~r1_tarski(k9_subset_1(k2_struct_0('#skF_4'), A_253, k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_122, c_92, c_42, c_122, c_2252])).
% 4.67/1.83  tff(c_2267, plain, (v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2')) | ~r1_tarski(k3_xboole_0(k2_struct_0('#skF_4'), '#skF_3'), k2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_268, c_2256])).
% 4.67/1.83  tff(c_2269, plain, (v3_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_156, c_182, c_110, c_36, c_156, c_182, c_268, c_2267])).
% 4.67/1.83  tff(c_2271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2269])).
% 4.67/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.83  
% 4.67/1.83  Inference rules
% 4.67/1.83  ----------------------
% 4.67/1.83  #Ref     : 0
% 4.67/1.83  #Sup     : 517
% 4.67/1.83  #Fact    : 0
% 4.67/1.83  #Define  : 0
% 4.67/1.83  #Split   : 3
% 4.67/1.83  #Chain   : 0
% 4.67/1.83  #Close   : 0
% 4.67/1.83  
% 4.67/1.83  Ordering : KBO
% 4.67/1.83  
% 4.67/1.83  Simplification rules
% 4.67/1.83  ----------------------
% 4.67/1.83  #Subsume      : 157
% 4.67/1.83  #Demod        : 297
% 4.67/1.83  #Tautology    : 197
% 4.67/1.83  #SimpNegUnit  : 1
% 4.67/1.83  #BackRed      : 3
% 4.67/1.83  
% 4.67/1.83  #Partial instantiations: 0
% 4.67/1.83  #Strategies tried      : 1
% 4.67/1.83  
% 4.67/1.83  Timing (in seconds)
% 4.67/1.83  ----------------------
% 4.67/1.83  Preprocessing        : 0.32
% 4.67/1.83  Parsing              : 0.17
% 4.67/1.83  CNF conversion       : 0.02
% 4.67/1.83  Main loop            : 0.74
% 4.67/1.83  Inferencing          : 0.29
% 4.67/1.83  Reduction            : 0.25
% 4.67/1.83  Demodulation         : 0.18
% 4.67/1.83  BG Simplification    : 0.03
% 4.67/1.83  Subsumption          : 0.13
% 4.67/1.83  Abstraction          : 0.04
% 4.67/1.83  MUC search           : 0.00
% 4.67/1.83  Cooper               : 0.00
% 4.67/1.83  Total                : 1.09
% 4.67/1.83  Index Insertion      : 0.00
% 4.67/1.83  Index Deletion       : 0.00
% 4.67/1.83  Index Matching       : 0.00
% 4.67/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
