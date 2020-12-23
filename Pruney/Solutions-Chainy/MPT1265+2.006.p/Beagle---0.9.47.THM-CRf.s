%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:42 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 347 expanded)
%              Number of leaves         :   32 ( 132 expanded)
%              Depth                    :   13
%              Number of atoms          :  151 ( 855 expanded)
%              Number of equality atoms :   35 ( 152 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & v1_tops_1(C,A)
                    & v3_pre_topc(C,A) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( v3_pre_topc(C,A)
                 => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_51,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_24,c_51])).

tff(c_60,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_42])).

tff(c_210,plain,(
    ! [A_69,B_70,C_71] :
      ( k9_subset_1(A_69,B_70,C_71) = k3_xboole_0(B_70,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_218,plain,(
    ! [B_70] : k9_subset_1(k2_struct_0('#skF_1'),B_70,'#skF_2') = k3_xboole_0(B_70,'#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_210])).

tff(c_363,plain,(
    ! [A_88,C_89,B_90] :
      ( k9_subset_1(A_88,C_89,B_90) = k9_subset_1(A_88,B_90,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_367,plain,(
    ! [B_90] : k9_subset_1(k2_struct_0('#skF_1'),B_90,'#skF_2') = k9_subset_1(k2_struct_0('#skF_1'),'#skF_2',B_90) ),
    inference(resolution,[status(thm)],[c_62,c_363])).

tff(c_375,plain,(
    ! [B_91] : k9_subset_1(k2_struct_0('#skF_1'),'#skF_2',B_91) = k3_xboole_0(B_91,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_367])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_61,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_40])).

tff(c_219,plain,(
    ! [B_70] : k9_subset_1(k2_struct_0('#skF_1'),B_70,'#skF_3') = k3_xboole_0(B_70,'#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_210])).

tff(c_386,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_219])).

tff(c_32,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_85,plain,(
    ~ v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_32])).

tff(c_229,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_85])).

tff(c_410,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_229])).

tff(c_38,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_533,plain,(
    ! [A_94,B_95] :
      ( k2_pre_topc(A_94,B_95) = k2_struct_0(A_94)
      | ~ v1_tops_1(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_540,plain,(
    ! [B_95] :
      ( k2_pre_topc('#skF_1',B_95) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_95,'#skF_1')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_533])).

tff(c_619,plain,(
    ! [B_96] :
      ( k2_pre_topc('#skF_1',B_96) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_96,'#skF_1')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_540])).

tff(c_629,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_61,c_619])).

tff(c_636,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_629])).

tff(c_369,plain,(
    ! [B_90] : k9_subset_1(k2_struct_0('#skF_1'),B_90,'#skF_3') = k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_90) ),
    inference(resolution,[status(thm)],[c_61,c_363])).

tff(c_374,plain,(
    ! [B_90] : k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_90) = k3_xboole_0(B_90,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_369])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_789,plain,(
    ! [A_106,C_107,B_108] :
      ( k2_pre_topc(A_106,k9_subset_1(u1_struct_0(A_106),C_107,B_108)) = k2_pre_topc(A_106,C_107)
      | ~ v3_pre_topc(C_107,A_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v1_tops_1(B_108,A_106)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_794,plain,(
    ! [C_107,B_108] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),C_107,B_108)) = k2_pre_topc('#skF_1',C_107)
      | ~ v3_pre_topc(C_107,'#skF_1')
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_108,'#skF_1')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_789])).

tff(c_800,plain,(
    ! [C_109,B_110] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),C_109,B_110)) = k2_pre_topc('#skF_1',C_109)
      | ~ v3_pre_topc(C_109,'#skF_1')
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_110,'#skF_1')
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_60,c_60,c_794])).

tff(c_807,plain,(
    ! [B_110] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_110)) = k2_pre_topc('#skF_1','#skF_3')
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ v1_tops_1(B_110,'#skF_1')
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_61,c_800])).

tff(c_1044,plain,(
    ! [B_124] :
      ( k2_pre_topc('#skF_1',k3_xboole_0(B_124,'#skF_3')) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_124,'#skF_1')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_636,c_374,c_807])).

tff(c_1051,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_1044])).

tff(c_1058,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_386,c_1051])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_435,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_8])).

tff(c_67,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_74,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_67])).

tff(c_109,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_129,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_52,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_74,c_109])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,(
    ! [A_5,A_52] :
      ( r1_tarski(A_5,k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_5,A_52)
      | ~ r1_tarski(A_52,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_129,c_10])).

tff(c_448,plain,
    ( r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k2_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_435,c_134])).

tff(c_457,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_448])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_664,plain,(
    ! [B_97,A_98] :
      ( v1_tops_1(B_97,A_98)
      | k2_pre_topc(A_98,B_97) != k2_struct_0(A_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1070,plain,(
    ! [A_125,A_126] :
      ( v1_tops_1(A_125,A_126)
      | k2_pre_topc(A_126,A_125) != k2_struct_0(A_126)
      | ~ l1_pre_topc(A_126)
      | ~ r1_tarski(A_125,u1_struct_0(A_126)) ) ),
    inference(resolution,[status(thm)],[c_20,c_664])).

tff(c_1081,plain,(
    ! [A_125] :
      ( v1_tops_1(A_125,'#skF_1')
      | k2_pre_topc('#skF_1',A_125) != k2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_125,k2_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1070])).

tff(c_1254,plain,(
    ! [A_132] :
      ( v1_tops_1(A_132,'#skF_1')
      | k2_pre_topc('#skF_1',A_132) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_132,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1081])).

tff(c_1275,plain,
    ( v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_457,c_1254])).

tff(c_1318,plain,(
    v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_1275])).

tff(c_1320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_1318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.66  
% 3.54/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.66  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.54/1.66  
% 3.54/1.66  %Foreground sorts:
% 3.54/1.66  
% 3.54/1.66  
% 3.54/1.66  %Background operators:
% 3.54/1.66  
% 3.54/1.66  
% 3.54/1.66  %Foreground operators:
% 3.54/1.66  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.54/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.54/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.54/1.66  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.54/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.54/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.54/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.54/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.54/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.54/1.66  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.54/1.66  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.54/1.66  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.54/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.54/1.66  
% 3.54/1.68  tff(f_105, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v1_tops_1(B, A) & v1_tops_1(C, A)) & v3_pre_topc(C, A)) => v1_tops_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_tops_1)).
% 3.54/1.68  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.54/1.68  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.54/1.68  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.54/1.68  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.54/1.68  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.54/1.68  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 3.54/1.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.54/1.68  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.54/1.68  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.54/1.68  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.54/1.68  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.54/1.68  tff(c_24, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.68  tff(c_51, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.54/1.68  tff(c_56, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_24, c_51])).
% 3.54/1.68  tff(c_60, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_56])).
% 3.54/1.68  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.54/1.68  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_42])).
% 3.54/1.68  tff(c_210, plain, (![A_69, B_70, C_71]: (k9_subset_1(A_69, B_70, C_71)=k3_xboole_0(B_70, C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.54/1.68  tff(c_218, plain, (![B_70]: (k9_subset_1(k2_struct_0('#skF_1'), B_70, '#skF_2')=k3_xboole_0(B_70, '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_210])).
% 3.54/1.68  tff(c_363, plain, (![A_88, C_89, B_90]: (k9_subset_1(A_88, C_89, B_90)=k9_subset_1(A_88, B_90, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.68  tff(c_367, plain, (![B_90]: (k9_subset_1(k2_struct_0('#skF_1'), B_90, '#skF_2')=k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', B_90))), inference(resolution, [status(thm)], [c_62, c_363])).
% 3.54/1.68  tff(c_375, plain, (![B_91]: (k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', B_91)=k3_xboole_0(B_91, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_367])).
% 3.54/1.68  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.54/1.68  tff(c_61, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_40])).
% 3.54/1.68  tff(c_219, plain, (![B_70]: (k9_subset_1(k2_struct_0('#skF_1'), B_70, '#skF_3')=k3_xboole_0(B_70, '#skF_3'))), inference(resolution, [status(thm)], [c_61, c_210])).
% 3.54/1.68  tff(c_386, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_375, c_219])).
% 3.54/1.68  tff(c_32, plain, (~v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.54/1.68  tff(c_85, plain, (~v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_32])).
% 3.54/1.68  tff(c_229, plain, (~v1_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_85])).
% 3.54/1.68  tff(c_410, plain, (~v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_229])).
% 3.54/1.68  tff(c_38, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.54/1.68  tff(c_34, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.54/1.68  tff(c_36, plain, (v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.54/1.68  tff(c_533, plain, (![A_94, B_95]: (k2_pre_topc(A_94, B_95)=k2_struct_0(A_94) | ~v1_tops_1(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.54/1.68  tff(c_540, plain, (![B_95]: (k2_pre_topc('#skF_1', B_95)=k2_struct_0('#skF_1') | ~v1_tops_1(B_95, '#skF_1') | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_533])).
% 3.54/1.68  tff(c_619, plain, (![B_96]: (k2_pre_topc('#skF_1', B_96)=k2_struct_0('#skF_1') | ~v1_tops_1(B_96, '#skF_1') | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_540])).
% 3.54/1.68  tff(c_629, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_61, c_619])).
% 3.54/1.68  tff(c_636, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_629])).
% 3.54/1.68  tff(c_369, plain, (![B_90]: (k9_subset_1(k2_struct_0('#skF_1'), B_90, '#skF_3')=k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_90))), inference(resolution, [status(thm)], [c_61, c_363])).
% 3.54/1.68  tff(c_374, plain, (![B_90]: (k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_90)=k3_xboole_0(B_90, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_369])).
% 3.54/1.68  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.54/1.68  tff(c_789, plain, (![A_106, C_107, B_108]: (k2_pre_topc(A_106, k9_subset_1(u1_struct_0(A_106), C_107, B_108))=k2_pre_topc(A_106, C_107) | ~v3_pre_topc(C_107, A_106) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~v1_tops_1(B_108, A_106) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.54/1.68  tff(c_794, plain, (![C_107, B_108]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), C_107, B_108))=k2_pre_topc('#skF_1', C_107) | ~v3_pre_topc(C_107, '#skF_1') | ~m1_subset_1(C_107, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_108, '#skF_1') | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_789])).
% 3.54/1.68  tff(c_800, plain, (![C_109, B_110]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), C_109, B_110))=k2_pre_topc('#skF_1', C_109) | ~v3_pre_topc(C_109, '#skF_1') | ~m1_subset_1(C_109, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_110, '#skF_1') | ~m1_subset_1(B_110, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_60, c_60, c_794])).
% 3.54/1.68  tff(c_807, plain, (![B_110]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_110))=k2_pre_topc('#skF_1', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1') | ~v1_tops_1(B_110, '#skF_1') | ~m1_subset_1(B_110, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_61, c_800])).
% 3.54/1.68  tff(c_1044, plain, (![B_124]: (k2_pre_topc('#skF_1', k3_xboole_0(B_124, '#skF_3'))=k2_struct_0('#skF_1') | ~v1_tops_1(B_124, '#skF_1') | ~m1_subset_1(B_124, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_636, c_374, c_807])).
% 3.54/1.68  tff(c_1051, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_1044])).
% 3.54/1.68  tff(c_1058, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_386, c_1051])).
% 3.54/1.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.68  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.54/1.68  tff(c_435, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_386, c_8])).
% 3.54/1.68  tff(c_67, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.54/1.68  tff(c_74, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_67])).
% 3.54/1.68  tff(c_109, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.68  tff(c_129, plain, (![A_52]: (r1_tarski(A_52, k2_struct_0('#skF_1')) | ~r1_tarski(A_52, '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_109])).
% 3.54/1.68  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.68  tff(c_134, plain, (![A_5, A_52]: (r1_tarski(A_5, k2_struct_0('#skF_1')) | ~r1_tarski(A_5, A_52) | ~r1_tarski(A_52, '#skF_2'))), inference(resolution, [status(thm)], [c_129, c_10])).
% 3.54/1.68  tff(c_448, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k2_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_435, c_134])).
% 3.54/1.68  tff(c_457, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_448])).
% 3.54/1.68  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.54/1.68  tff(c_664, plain, (![B_97, A_98]: (v1_tops_1(B_97, A_98) | k2_pre_topc(A_98, B_97)!=k2_struct_0(A_98) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.54/1.68  tff(c_1070, plain, (![A_125, A_126]: (v1_tops_1(A_125, A_126) | k2_pre_topc(A_126, A_125)!=k2_struct_0(A_126) | ~l1_pre_topc(A_126) | ~r1_tarski(A_125, u1_struct_0(A_126)))), inference(resolution, [status(thm)], [c_20, c_664])).
% 3.54/1.68  tff(c_1081, plain, (![A_125]: (v1_tops_1(A_125, '#skF_1') | k2_pre_topc('#skF_1', A_125)!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_125, k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1070])).
% 3.54/1.68  tff(c_1254, plain, (![A_132]: (v1_tops_1(A_132, '#skF_1') | k2_pre_topc('#skF_1', A_132)!=k2_struct_0('#skF_1') | ~r1_tarski(A_132, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1081])).
% 3.54/1.68  tff(c_1275, plain, (v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_457, c_1254])).
% 3.54/1.68  tff(c_1318, plain, (v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_1275])).
% 3.54/1.68  tff(c_1320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_410, c_1318])).
% 3.54/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.68  
% 3.54/1.68  Inference rules
% 3.54/1.68  ----------------------
% 3.54/1.68  #Ref     : 0
% 3.54/1.68  #Sup     : 317
% 3.54/1.68  #Fact    : 0
% 3.54/1.68  #Define  : 0
% 3.54/1.68  #Split   : 3
% 3.54/1.68  #Chain   : 0
% 3.54/1.68  #Close   : 0
% 3.54/1.68  
% 3.54/1.68  Ordering : KBO
% 3.54/1.68  
% 3.54/1.68  Simplification rules
% 3.54/1.68  ----------------------
% 3.54/1.68  #Subsume      : 44
% 3.54/1.68  #Demod        : 105
% 3.54/1.68  #Tautology    : 82
% 3.54/1.68  #SimpNegUnit  : 1
% 3.54/1.68  #BackRed      : 4
% 3.54/1.68  
% 3.54/1.68  #Partial instantiations: 0
% 3.54/1.68  #Strategies tried      : 1
% 3.54/1.68  
% 3.54/1.68  Timing (in seconds)
% 3.54/1.68  ----------------------
% 3.54/1.68  Preprocessing        : 0.40
% 3.54/1.68  Parsing              : 0.20
% 3.54/1.68  CNF conversion       : 0.03
% 3.54/1.68  Main loop            : 0.46
% 3.54/1.68  Inferencing          : 0.15
% 3.54/1.68  Reduction            : 0.15
% 3.54/1.68  Demodulation         : 0.11
% 3.54/1.68  BG Simplification    : 0.03
% 3.54/1.68  Subsumption          : 0.09
% 3.54/1.68  Abstraction          : 0.03
% 3.54/1.68  MUC search           : 0.00
% 3.54/1.68  Cooper               : 0.00
% 3.54/1.68  Total                : 0.89
% 3.54/1.68  Index Insertion      : 0.00
% 3.54/1.68  Index Deletion       : 0.00
% 3.54/1.68  Index Matching       : 0.00
% 3.54/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
