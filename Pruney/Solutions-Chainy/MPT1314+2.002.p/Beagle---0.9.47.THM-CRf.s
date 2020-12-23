%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:59 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 298 expanded)
%              Number of leaves         :   35 ( 118 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 705 expanded)
%              Number of equality atoms :   26 ( 135 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_105,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_87,axiom,(
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

tff(c_36,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    ~ v3_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_118,plain,(
    ! [B_69,A_70] :
      ( l1_pre_topc(B_69)
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_118])).

tff(c_124,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_121])).

tff(c_22,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    ! [A_23] :
      ( u1_struct_0(A_23) = k2_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_22,c_54])).

tff(c_128,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_124,c_58])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_47,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38])).

tff(c_129,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_47])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_216,plain,(
    ! [C_84,A_85,B_86] :
      ( r2_hidden(C_84,A_85)
      | ~ r2_hidden(C_84,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_309,plain,(
    ! [A_103,B_104,A_105] :
      ( r2_hidden('#skF_1'(A_103,B_104),A_105)
      | ~ m1_subset_1(A_103,k1_zfmisc_1(A_105))
      | r1_tarski(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_6,c_216])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_321,plain,(
    ! [A_106,A_107] :
      ( ~ m1_subset_1(A_106,k1_zfmisc_1(A_107))
      | r1_tarski(A_106,A_107) ) ),
    inference(resolution,[status(thm)],[c_309,c_4])).

tff(c_328,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_129,c_321])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_337,plain,(
    k3_xboole_0('#skF_4',k2_struct_0('#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_328,c_8])).

tff(c_10,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_102,plain,(
    ! [A_65,B_66] : k1_setfam_1(k2_tarski(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_135,plain,(
    ! [A_73,B_74] : k1_setfam_1(k2_tarski(A_73,B_74)) = k3_xboole_0(B_74,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_102])).

tff(c_18,plain,(
    ! [A_20,B_21] : k1_setfam_1(k2_tarski(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_141,plain,(
    ! [B_74,A_73] : k3_xboole_0(B_74,A_73) = k3_xboole_0(A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_18])).

tff(c_92,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_22,c_54])).

tff(c_96,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_92])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_97,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_44])).

tff(c_40,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_220,plain,(
    ! [A_87,B_88,C_89] :
      ( k9_subset_1(A_87,B_88,C_89) = k3_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_225,plain,(
    ! [B_88] : k9_subset_1(k2_struct_0('#skF_5'),B_88,'#skF_4') = k3_xboole_0(B_88,'#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_220])).

tff(c_257,plain,(
    ! [A_95,C_96,B_97] :
      ( k9_subset_1(A_95,C_96,B_97) = k9_subset_1(A_95,B_97,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_259,plain,(
    ! [B_97] : k9_subset_1(k2_struct_0('#skF_5'),B_97,'#skF_4') = k9_subset_1(k2_struct_0('#skF_5'),'#skF_4',B_97) ),
    inference(resolution,[status(thm)],[c_129,c_257])).

tff(c_263,plain,(
    ! [B_97] : k9_subset_1(k2_struct_0('#skF_5'),'#skF_4',B_97) = k3_xboole_0(B_97,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_259])).

tff(c_651,plain,(
    ! [B_133,D_134,A_135] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_133),D_134,k2_struct_0(B_133)),B_133)
      | ~ v3_pre_topc(D_134,A_135)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_133),D_134,k2_struct_0(B_133)),k1_zfmisc_1(u1_struct_0(B_133)))
      | ~ m1_pre_topc(B_133,A_135)
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_657,plain,(
    ! [B_133,D_134] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_133),D_134,k2_struct_0(B_133)),B_133)
      | ~ v3_pre_topc(D_134,'#skF_3')
      | ~ m1_subset_1(D_134,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_133),D_134,k2_struct_0(B_133)),k1_zfmisc_1(u1_struct_0(B_133)))
      | ~ m1_pre_topc(B_133,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_651])).

tff(c_1493,plain,(
    ! [B_282,D_283] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_282),D_283,k2_struct_0(B_282)),B_282)
      | ~ v3_pre_topc(D_283,'#skF_3')
      | ~ m1_subset_1(D_283,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_282),D_283,k2_struct_0(B_282)),k1_zfmisc_1(u1_struct_0(B_282)))
      | ~ m1_pre_topc(B_282,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_657])).

tff(c_1503,plain,(
    ! [D_283] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_5'),D_283,k2_struct_0('#skF_5')),'#skF_5')
      | ~ v3_pre_topc(D_283,'#skF_3')
      | ~ m1_subset_1(D_283,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_5'),D_283,k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_1493])).

tff(c_1831,plain,(
    ! [D_335] :
      ( v3_pre_topc(k9_subset_1(k2_struct_0('#skF_5'),D_335,k2_struct_0('#skF_5')),'#skF_5')
      | ~ v3_pre_topc(D_335,'#skF_3')
      | ~ m1_subset_1(D_335,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_5'),D_335,k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_128,c_128,c_1503])).

tff(c_1838,plain,
    ( v3_pre_topc(k9_subset_1(k2_struct_0('#skF_5'),'#skF_4',k2_struct_0('#skF_5')),'#skF_5')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_subset_1(k3_xboole_0(k2_struct_0('#skF_5'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_1831])).

tff(c_1840,plain,(
    v3_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_337,c_141,c_97,c_40,c_337,c_141,c_263,c_1838])).

tff(c_1842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:38:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.83  
% 4.71/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.78/1.83  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 4.78/1.83  
% 4.78/1.83  %Foreground sorts:
% 4.78/1.83  
% 4.78/1.83  
% 4.78/1.83  %Background operators:
% 4.78/1.83  
% 4.78/1.83  
% 4.78/1.83  %Foreground operators:
% 4.78/1.83  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.78/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.78/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.78/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.78/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.78/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.78/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.78/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.78/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.78/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.78/1.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.78/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.78/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.83  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.78/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.78/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.78/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.78/1.83  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.78/1.83  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.78/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.78/1.83  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.78/1.83  
% 4.78/1.85  tff(f_105, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 4.78/1.85  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.78/1.85  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.78/1.85  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.78/1.85  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.78/1.85  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.78/1.85  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.78/1.85  tff(f_38, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.78/1.85  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.78/1.85  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.78/1.85  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.78/1.85  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_2)).
% 4.78/1.85  tff(c_36, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.78/1.85  tff(c_34, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.78/1.85  tff(c_48, plain, (~v3_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 4.78/1.85  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.78/1.85  tff(c_42, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.78/1.85  tff(c_118, plain, (![B_69, A_70]: (l1_pre_topc(B_69) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.78/1.85  tff(c_121, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_118])).
% 4.78/1.85  tff(c_124, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_121])).
% 4.78/1.85  tff(c_22, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.78/1.85  tff(c_54, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.78/1.85  tff(c_58, plain, (![A_23]: (u1_struct_0(A_23)=k2_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(resolution, [status(thm)], [c_22, c_54])).
% 4.78/1.85  tff(c_128, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_124, c_58])).
% 4.78/1.85  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.78/1.85  tff(c_47, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38])).
% 4.78/1.85  tff(c_129, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_47])).
% 4.78/1.85  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.78/1.85  tff(c_216, plain, (![C_84, A_85, B_86]: (r2_hidden(C_84, A_85) | ~r2_hidden(C_84, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.78/1.85  tff(c_309, plain, (![A_103, B_104, A_105]: (r2_hidden('#skF_1'(A_103, B_104), A_105) | ~m1_subset_1(A_103, k1_zfmisc_1(A_105)) | r1_tarski(A_103, B_104))), inference(resolution, [status(thm)], [c_6, c_216])).
% 4.78/1.85  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.78/1.85  tff(c_321, plain, (![A_106, A_107]: (~m1_subset_1(A_106, k1_zfmisc_1(A_107)) | r1_tarski(A_106, A_107))), inference(resolution, [status(thm)], [c_309, c_4])).
% 4.78/1.85  tff(c_328, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_129, c_321])).
% 4.78/1.85  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.78/1.85  tff(c_337, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_328, c_8])).
% 4.78/1.85  tff(c_10, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.78/1.85  tff(c_102, plain, (![A_65, B_66]: (k1_setfam_1(k2_tarski(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.78/1.85  tff(c_135, plain, (![A_73, B_74]: (k1_setfam_1(k2_tarski(A_73, B_74))=k3_xboole_0(B_74, A_73))), inference(superposition, [status(thm), theory('equality')], [c_10, c_102])).
% 4.78/1.85  tff(c_18, plain, (![A_20, B_21]: (k1_setfam_1(k2_tarski(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.78/1.85  tff(c_141, plain, (![B_74, A_73]: (k3_xboole_0(B_74, A_73)=k3_xboole_0(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_135, c_18])).
% 4.78/1.85  tff(c_92, plain, (![A_64]: (u1_struct_0(A_64)=k2_struct_0(A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_22, c_54])).
% 4.78/1.85  tff(c_96, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_92])).
% 4.78/1.85  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.78/1.85  tff(c_97, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_44])).
% 4.78/1.85  tff(c_40, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.78/1.85  tff(c_220, plain, (![A_87, B_88, C_89]: (k9_subset_1(A_87, B_88, C_89)=k3_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.78/1.85  tff(c_225, plain, (![B_88]: (k9_subset_1(k2_struct_0('#skF_5'), B_88, '#skF_4')=k3_xboole_0(B_88, '#skF_4'))), inference(resolution, [status(thm)], [c_129, c_220])).
% 4.78/1.85  tff(c_257, plain, (![A_95, C_96, B_97]: (k9_subset_1(A_95, C_96, B_97)=k9_subset_1(A_95, B_97, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.78/1.85  tff(c_259, plain, (![B_97]: (k9_subset_1(k2_struct_0('#skF_5'), B_97, '#skF_4')=k9_subset_1(k2_struct_0('#skF_5'), '#skF_4', B_97))), inference(resolution, [status(thm)], [c_129, c_257])).
% 4.78/1.85  tff(c_263, plain, (![B_97]: (k9_subset_1(k2_struct_0('#skF_5'), '#skF_4', B_97)=k3_xboole_0(B_97, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_259])).
% 4.78/1.85  tff(c_651, plain, (![B_133, D_134, A_135]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_133), D_134, k2_struct_0(B_133)), B_133) | ~v3_pre_topc(D_134, A_135) | ~m1_subset_1(D_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_133), D_134, k2_struct_0(B_133)), k1_zfmisc_1(u1_struct_0(B_133))) | ~m1_pre_topc(B_133, A_135) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.78/1.85  tff(c_657, plain, (![B_133, D_134]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_133), D_134, k2_struct_0(B_133)), B_133) | ~v3_pre_topc(D_134, '#skF_3') | ~m1_subset_1(D_134, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_133), D_134, k2_struct_0(B_133)), k1_zfmisc_1(u1_struct_0(B_133))) | ~m1_pre_topc(B_133, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_651])).
% 4.78/1.85  tff(c_1493, plain, (![B_282, D_283]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_282), D_283, k2_struct_0(B_282)), B_282) | ~v3_pre_topc(D_283, '#skF_3') | ~m1_subset_1(D_283, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_282), D_283, k2_struct_0(B_282)), k1_zfmisc_1(u1_struct_0(B_282))) | ~m1_pre_topc(B_282, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_657])).
% 4.78/1.85  tff(c_1503, plain, (![D_283]: (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_5'), D_283, k2_struct_0('#skF_5')), '#skF_5') | ~v3_pre_topc(D_283, '#skF_3') | ~m1_subset_1(D_283, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(k2_struct_0('#skF_5'), D_283, k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_1493])).
% 4.78/1.85  tff(c_1831, plain, (![D_335]: (v3_pre_topc(k9_subset_1(k2_struct_0('#skF_5'), D_335, k2_struct_0('#skF_5')), '#skF_5') | ~v3_pre_topc(D_335, '#skF_3') | ~m1_subset_1(D_335, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(k2_struct_0('#skF_5'), D_335, k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_128, c_128, c_1503])).
% 4.78/1.85  tff(c_1838, plain, (v3_pre_topc(k9_subset_1(k2_struct_0('#skF_5'), '#skF_4', k2_struct_0('#skF_5')), '#skF_5') | ~v3_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k3_xboole_0(k2_struct_0('#skF_5'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_263, c_1831])).
% 4.78/1.85  tff(c_1840, plain, (v3_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_337, c_141, c_97, c_40, c_337, c_141, c_263, c_1838])).
% 4.78/1.85  tff(c_1842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1840])).
% 4.78/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.78/1.85  
% 4.78/1.85  Inference rules
% 4.78/1.85  ----------------------
% 4.78/1.85  #Ref     : 0
% 4.78/1.85  #Sup     : 461
% 4.78/1.85  #Fact    : 0
% 4.78/1.85  #Define  : 0
% 4.78/1.85  #Split   : 7
% 4.78/1.85  #Chain   : 0
% 4.78/1.85  #Close   : 0
% 4.78/1.85  
% 4.78/1.85  Ordering : KBO
% 4.78/1.85  
% 4.78/1.85  Simplification rules
% 4.78/1.85  ----------------------
% 4.78/1.85  #Subsume      : 175
% 4.78/1.85  #Demod        : 123
% 4.78/1.85  #Tautology    : 108
% 4.78/1.85  #SimpNegUnit  : 1
% 4.78/1.85  #BackRed      : 2
% 4.78/1.85  
% 4.78/1.85  #Partial instantiations: 0
% 4.78/1.85  #Strategies tried      : 1
% 4.78/1.85  
% 4.78/1.85  Timing (in seconds)
% 4.78/1.85  ----------------------
% 4.78/1.85  Preprocessing        : 0.33
% 4.78/1.85  Parsing              : 0.17
% 4.78/1.85  CNF conversion       : 0.03
% 4.78/1.85  Main loop            : 0.76
% 4.78/1.85  Inferencing          : 0.25
% 4.78/1.85  Reduction            : 0.24
% 4.78/1.85  Demodulation         : 0.18
% 4.78/1.85  BG Simplification    : 0.03
% 4.78/1.85  Subsumption          : 0.19
% 4.78/1.85  Abstraction          : 0.03
% 4.78/1.85  MUC search           : 0.00
% 4.78/1.85  Cooper               : 0.00
% 4.78/1.85  Total                : 1.12
% 4.78/1.85  Index Insertion      : 0.00
% 4.78/1.85  Index Deletion       : 0.00
% 4.78/1.85  Index Matching       : 0.00
% 4.78/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
