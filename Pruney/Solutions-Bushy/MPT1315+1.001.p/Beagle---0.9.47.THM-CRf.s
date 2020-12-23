%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1315+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:47 EST 2020

% Result     : Theorem 11.44s
% Output     : CNFRefutation 11.50s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 280 expanded)
%              Number of leaves         :   29 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 678 expanded)
%              Number of equality atoms :   22 ( 125 expanded)
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

tff(f_96,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_78,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

tff(c_32,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ~ v4_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_129,plain,(
    ! [B_65,A_66] :
      ( l1_pre_topc(B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_132,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_135,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_132])).

tff(c_10,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    ! [A_10] :
      ( u1_struct_0(A_10) = k2_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_10,c_50])).

tff(c_139,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_135,c_54])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_43,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_99,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_107,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_43,c_99])).

tff(c_141,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_107])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_116,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_107,c_16])).

tff(c_140,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_116])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_88,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_10,c_50])).

tff(c_92,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_88])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_93,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_40])).

tff(c_106,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_93,c_99])).

tff(c_36,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_142,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_43])).

tff(c_172,plain,(
    ! [A_73,B_74,C_75] :
      ( k9_subset_1(A_73,B_74,C_75) = k3_xboole_0(B_74,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_181,plain,(
    ! [B_74] : k9_subset_1(k2_struct_0('#skF_4'),B_74,'#skF_3') = k3_xboole_0(B_74,'#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_172])).

tff(c_256,plain,(
    ! [A_80,C_81,B_82] :
      ( k9_subset_1(A_80,C_81,B_82) = k9_subset_1(A_80,B_82,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_260,plain,(
    ! [B_82] : k9_subset_1(k2_struct_0('#skF_4'),B_82,'#skF_3') = k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',B_82) ),
    inference(resolution,[status(thm)],[c_142,c_256])).

tff(c_269,plain,(
    ! [B_82] : k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',B_82) = k3_xboole_0(B_82,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_260])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1009,plain,(
    ! [B_116,D_117,A_118] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_116),D_117,k2_struct_0(B_116)),B_116)
      | ~ v4_pre_topc(D_117,A_118)
      | ~ m1_subset_1(D_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_116),D_117,k2_struct_0(B_116)),k1_zfmisc_1(u1_struct_0(B_116)))
      | ~ m1_pre_topc(B_116,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3360,plain,(
    ! [B_217,A_218,A_219] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_217),A_218,k2_struct_0(B_217)),B_217)
      | ~ v4_pre_topc(A_218,A_219)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_217),A_218,k2_struct_0(B_217)),k1_zfmisc_1(u1_struct_0(B_217)))
      | ~ m1_pre_topc(B_217,A_219)
      | ~ l1_pre_topc(A_219)
      | ~ r1_tarski(A_218,u1_struct_0(A_219)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1009])).

tff(c_19200,plain,(
    ! [B_428,A_429,A_430] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_428),A_429,k2_struct_0(B_428)),B_428)
      | ~ v4_pre_topc(A_429,A_430)
      | ~ m1_pre_topc(B_428,A_430)
      | ~ l1_pre_topc(A_430)
      | ~ r1_tarski(A_429,u1_struct_0(A_430))
      | ~ r1_tarski(k9_subset_1(u1_struct_0(B_428),A_429,k2_struct_0(B_428)),u1_struct_0(B_428)) ) ),
    inference(resolution,[status(thm)],[c_20,c_3360])).

tff(c_19202,plain,(
    ! [A_429] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),A_429,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(A_429,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_429,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),A_429,k2_struct_0('#skF_4')),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_19200])).

tff(c_19209,plain,(
    ! [A_431] :
      ( v4_pre_topc(k9_subset_1(k2_struct_0('#skF_4'),A_431,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(A_431,'#skF_2')
      | ~ r1_tarski(A_431,k2_struct_0('#skF_2'))
      | ~ r1_tarski(k9_subset_1(k2_struct_0('#skF_4'),A_431,k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_92,c_42,c_139,c_19202])).

tff(c_19229,plain,
    ( v4_pre_topc(k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',k2_struct_0('#skF_4')),'#skF_4')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2'))
    | ~ r1_tarski(k3_xboole_0(k2_struct_0('#skF_4'),'#skF_3'),k2_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_19209])).

tff(c_19239,plain,(
    v4_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_140,c_2,c_106,c_36,c_140,c_2,c_269,c_19229])).

tff(c_19241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_19239])).

%------------------------------------------------------------------------------
