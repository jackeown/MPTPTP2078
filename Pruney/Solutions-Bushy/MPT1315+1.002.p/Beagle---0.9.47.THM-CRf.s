%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1315+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:47 EST 2020

% Result     : Theorem 7.42s
% Output     : CNFRefutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 334 expanded)
%              Number of leaves         :   29 ( 125 expanded)
%              Depth                    :   16
%              Number of atoms          :  127 ( 782 expanded)
%              Number of equality atoms :   17 ( 114 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v4_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v4_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v4_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

tff(c_30,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    ~ v4_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_48,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_54,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_58,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_54])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_59,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_38])).

tff(c_65,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_75,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_59,c_65])).

tff(c_34,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_78,plain,(
    ! [B_59,A_60] :
      ( l1_pre_topc(B_59)
      | ~ m1_pre_topc(B_59,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_78])).

tff(c_84,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81])).

tff(c_52,plain,(
    ! [A_6] :
      ( u1_struct_0(A_6) = k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_88,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_52])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_41,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_77,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_41,c_65])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_77,c_14])).

tff(c_107,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_92])).

tff(c_122,plain,(
    ! [A_61] :
      ( m1_subset_1(k2_struct_0(A_61),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_133,plain,(
    ! [A_62] :
      ( r1_tarski(k2_struct_0(A_62),u1_struct_0(A_62))
      | ~ l1_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_122,c_16])).

tff(c_139,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_133])).

tff(c_144,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_147,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_144])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_147])).

tff(c_153,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_128,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_122])).

tff(c_237,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_128])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( k9_subset_1(A_10,B_11,C_12) = k3_xboole_0(B_11,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_438,plain,(
    ! [B_90] : k9_subset_1(k2_struct_0('#skF_4'),B_90,k2_struct_0('#skF_4')) = k3_xboole_0(B_90,k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_237,c_12])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_447,plain,(
    ! [B_90] :
      ( m1_subset_1(k3_xboole_0(B_90,k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_6])).

tff(c_455,plain,(
    ! [B_90] : m1_subset_1(k3_xboole_0(B_90,k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_447])).

tff(c_243,plain,(
    ! [B_11] : k9_subset_1(k2_struct_0('#skF_4'),B_11,k2_struct_0('#skF_4')) = k3_xboole_0(B_11,k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_237,c_12])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_981,plain,(
    ! [B_130,D_131,A_132] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_130),D_131,k2_struct_0(B_130)),B_130)
      | ~ v4_pre_topc(D_131,A_132)
      | ~ m1_subset_1(D_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_130),D_131,k2_struct_0(B_130)),k1_zfmisc_1(u1_struct_0(B_130)))
      | ~ m1_pre_topc(B_130,A_132)
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2763,plain,(
    ! [B_296,A_297,A_298] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_296),A_297,k2_struct_0(B_296)),B_296)
      | ~ v4_pre_topc(A_297,A_298)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_296),A_297,k2_struct_0(B_296)),k1_zfmisc_1(u1_struct_0(B_296)))
      | ~ m1_pre_topc(B_296,A_298)
      | ~ l1_pre_topc(A_298)
      | ~ r1_tarski(A_297,u1_struct_0(A_298)) ) ),
    inference(resolution,[status(thm)],[c_18,c_981])).

tff(c_2774,plain,(
    ! [A_297,A_298] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),A_297,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(A_297,A_298)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'),A_297,k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_298)
      | ~ l1_pre_topc(A_298)
      | ~ r1_tarski(A_297,u1_struct_0(A_298)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_2763])).

tff(c_6107,plain,(
    ! [A_550,A_551] :
      ( v4_pre_topc(k3_xboole_0(A_550,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(A_550,A_551)
      | ~ m1_pre_topc('#skF_4',A_551)
      | ~ l1_pre_topc(A_551)
      | ~ r1_tarski(A_550,u1_struct_0(A_551)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_243,c_88,c_243,c_88,c_2774])).

tff(c_6123,plain,(
    ! [A_550] :
      ( v4_pre_topc(k3_xboole_0(A_550,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(A_550,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_550,k2_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_6107])).

tff(c_6133,plain,(
    ! [A_552] :
      ( v4_pre_topc(k3_xboole_0(A_552,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(A_552,'#skF_2')
      | ~ r1_tarski(A_552,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_6123])).

tff(c_6164,plain,
    ( v4_pre_topc('#skF_3','#skF_4')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_6133])).

tff(c_6172,plain,(
    v4_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_34,c_6164])).

tff(c_6174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_6172])).

%------------------------------------------------------------------------------
