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
% DateTime   : Thu Dec  3 10:21:33 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 185 expanded)
%              Number of leaves         :   38 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 362 expanded)
%              Number of equality atoms :   54 ( 111 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_76,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1277,plain,(
    ! [A_174,B_175,C_176] :
      ( k7_subset_1(A_174,B_175,C_176) = k4_xboole_0(B_175,C_176)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(A_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1285,plain,(
    ! [C_176] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_176) = k4_xboole_0('#skF_2',C_176) ),
    inference(resolution,[status(thm)],[c_38,c_1277])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_83,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_449,plain,(
    ! [B_101,A_102] :
      ( v4_pre_topc(B_101,A_102)
      | k2_pre_topc(A_102,B_101) != B_101
      | ~ v2_pre_topc(A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_459,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_449])).

tff(c_468,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_459])).

tff(c_469,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_468])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_146,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_50])).

tff(c_156,plain,(
    ! [A_60,B_61,C_62] :
      ( k7_subset_1(A_60,B_61,C_62) = k4_xboole_0(B_61,C_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_175,plain,(
    ! [C_65] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_65) = k4_xboole_0('#skF_2',C_65) ),
    inference(resolution,[status(thm)],[c_38,c_156])).

tff(c_187,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_175])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( k4_subset_1(A_18,B_19,k2_subset_1(A_18)) = k2_subset_1(A_18)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [A_53,B_54] :
      ( k4_subset_1(A_53,B_54,A_53) = A_53
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_18])).

tff(c_126,plain,(
    ! [B_56,A_57] :
      ( k4_subset_1(B_56,A_57,B_56) = B_56
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_136,plain,(
    ! [A_3,B_4] : k4_subset_1(A_3,k4_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_207,plain,(
    k4_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_136])).

tff(c_210,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_4])).

tff(c_12,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_355,plain,(
    ! [A_92,C_93,B_94] :
      ( k4_subset_1(A_92,C_93,B_94) = k4_subset_1(A_92,B_94,C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(A_92))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_471,plain,(
    ! [A_103,B_104] :
      ( k4_subset_1(A_103,B_104,A_103) = k4_subset_1(A_103,A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(resolution,[status(thm)],[c_51,c_355])).

tff(c_520,plain,(
    ! [B_106,A_107] :
      ( k4_subset_1(B_106,B_106,A_107) = k4_subset_1(B_106,A_107,B_106)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(resolution,[status(thm)],[c_24,c_471])).

tff(c_524,plain,(
    k4_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k4_subset_1('#skF_2','#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_210,c_520])).

tff(c_533,plain,(
    k4_subset_1('#skF_2','#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_524])).

tff(c_327,plain,(
    ! [A_87,B_88,C_89] :
      ( k4_subset_1(A_87,B_88,C_89) = k2_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_626,plain,(
    ! [B_114,B_115,A_116] :
      ( k4_subset_1(B_114,B_115,A_116) = k2_xboole_0(B_115,A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(B_114))
      | ~ r1_tarski(A_116,B_114) ) ),
    inference(resolution,[status(thm)],[c_24,c_327])).

tff(c_639,plain,(
    ! [A_117,A_118] :
      ( k4_subset_1(A_117,A_117,A_118) = k2_xboole_0(A_117,A_118)
      | ~ r1_tarski(A_118,A_117) ) ),
    inference(resolution,[status(thm)],[c_51,c_626])).

tff(c_643,plain,(
    k4_subset_1('#skF_2','#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_210,c_639])).

tff(c_652,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_643])).

tff(c_556,plain,(
    ! [A_110,B_111] :
      ( k4_subset_1(u1_struct_0(A_110),B_111,k2_tops_1(A_110,B_111)) = k2_pre_topc(A_110,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_563,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_556])).

tff(c_571,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_563])).

tff(c_280,plain,(
    ! [A_79,B_80] :
      ( m1_subset_1(k2_tops_1(A_79,B_80),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_297,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k2_tops_1(A_79,B_80),u1_struct_0(A_79))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_280,c_22])).

tff(c_685,plain,(
    ! [A_123] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_123) = k2_xboole_0('#skF_2',A_123)
      | ~ r1_tarski(A_123,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_38,c_626])).

tff(c_689,plain,(
    ! [B_80] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_80)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_80))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_297,c_685])).

tff(c_1183,plain,(
    ! [B_160] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_160)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_160))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_689])).

tff(c_1194,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_1183])).

tff(c_1204,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_571,c_1194])).

tff(c_1206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_469,c_1204])).

tff(c_1207,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1317,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_1207])).

tff(c_1208,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1296,plain,(
    ! [A_179,B_180] :
      ( k2_pre_topc(A_179,B_180) = B_180
      | ~ v4_pre_topc(B_180,A_179)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1303,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1296])).

tff(c_1311,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1208,c_1303])).

tff(c_1900,plain,(
    ! [A_255,B_256] :
      ( k7_subset_1(u1_struct_0(A_255),k2_pre_topc(A_255,B_256),k1_tops_1(A_255,B_256)) = k2_tops_1(A_255,B_256)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1909,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1311,c_1900])).

tff(c_1913,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1285,c_1909])).

tff(c_1915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1317,c_1913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.73  
% 4.07/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.73  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 4.07/1.73  
% 4.07/1.73  %Foreground sorts:
% 4.07/1.73  
% 4.07/1.73  
% 4.07/1.73  %Background operators:
% 4.07/1.73  
% 4.07/1.73  
% 4.07/1.73  %Foreground operators:
% 4.07/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.07/1.73  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.07/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.07/1.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.07/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.07/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.07/1.73  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.07/1.73  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.07/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.07/1.73  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.07/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.07/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.07/1.73  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.07/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.07/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.07/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.07/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.07/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.07/1.73  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.07/1.73  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.07/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.07/1.73  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.07/1.73  
% 4.07/1.75  tff(f_116, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.07/1.75  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.07/1.75  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.07/1.75  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.07/1.75  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.07/1.75  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.07/1.75  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 4.07/1.75  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.07/1.75  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 4.07/1.75  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.07/1.75  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.07/1.75  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.07/1.75  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.07/1.75  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.07/1.75  tff(c_1277, plain, (![A_174, B_175, C_176]: (k7_subset_1(A_174, B_175, C_176)=k4_xboole_0(B_175, C_176) | ~m1_subset_1(B_175, k1_zfmisc_1(A_174)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.07/1.75  tff(c_1285, plain, (![C_176]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_176)=k4_xboole_0('#skF_2', C_176))), inference(resolution, [status(thm)], [c_38, c_1277])).
% 4.07/1.75  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.07/1.75  tff(c_83, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.07/1.75  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.07/1.75  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.07/1.75  tff(c_449, plain, (![B_101, A_102]: (v4_pre_topc(B_101, A_102) | k2_pre_topc(A_102, B_101)!=B_101 | ~v2_pre_topc(A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.07/1.75  tff(c_459, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_449])).
% 4.07/1.75  tff(c_468, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_459])).
% 4.07/1.75  tff(c_469, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_83, c_468])).
% 4.07/1.75  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.07/1.75  tff(c_146, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_83, c_50])).
% 4.07/1.75  tff(c_156, plain, (![A_60, B_61, C_62]: (k7_subset_1(A_60, B_61, C_62)=k4_xboole_0(B_61, C_62) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.07/1.75  tff(c_175, plain, (![C_65]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_65)=k4_xboole_0('#skF_2', C_65))), inference(resolution, [status(thm)], [c_38, c_156])).
% 4.07/1.75  tff(c_187, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_146, c_175])).
% 4.07/1.75  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.07/1.75  tff(c_24, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.07/1.75  tff(c_10, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.07/1.75  tff(c_18, plain, (![A_18, B_19]: (k4_subset_1(A_18, B_19, k2_subset_1(A_18))=k2_subset_1(A_18) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.07/1.75  tff(c_107, plain, (![A_53, B_54]: (k4_subset_1(A_53, B_54, A_53)=A_53 | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_18])).
% 4.07/1.75  tff(c_126, plain, (![B_56, A_57]: (k4_subset_1(B_56, A_57, B_56)=B_56 | ~r1_tarski(A_57, B_56))), inference(resolution, [status(thm)], [c_24, c_107])).
% 4.07/1.75  tff(c_136, plain, (![A_3, B_4]: (k4_subset_1(A_3, k4_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_126])).
% 4.07/1.75  tff(c_207, plain, (k4_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_187, c_136])).
% 4.07/1.75  tff(c_210, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_187, c_4])).
% 4.07/1.75  tff(c_12, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.07/1.75  tff(c_51, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 4.07/1.75  tff(c_355, plain, (![A_92, C_93, B_94]: (k4_subset_1(A_92, C_93, B_94)=k4_subset_1(A_92, B_94, C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(A_92)) | ~m1_subset_1(B_94, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.07/1.75  tff(c_471, plain, (![A_103, B_104]: (k4_subset_1(A_103, B_104, A_103)=k4_subset_1(A_103, A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(resolution, [status(thm)], [c_51, c_355])).
% 4.07/1.75  tff(c_520, plain, (![B_106, A_107]: (k4_subset_1(B_106, B_106, A_107)=k4_subset_1(B_106, A_107, B_106) | ~r1_tarski(A_107, B_106))), inference(resolution, [status(thm)], [c_24, c_471])).
% 4.07/1.75  tff(c_524, plain, (k4_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k4_subset_1('#skF_2', '#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_210, c_520])).
% 4.07/1.75  tff(c_533, plain, (k4_subset_1('#skF_2', '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_207, c_524])).
% 4.07/1.75  tff(c_327, plain, (![A_87, B_88, C_89]: (k4_subset_1(A_87, B_88, C_89)=k2_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.07/1.75  tff(c_626, plain, (![B_114, B_115, A_116]: (k4_subset_1(B_114, B_115, A_116)=k2_xboole_0(B_115, A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(B_114)) | ~r1_tarski(A_116, B_114))), inference(resolution, [status(thm)], [c_24, c_327])).
% 4.07/1.75  tff(c_639, plain, (![A_117, A_118]: (k4_subset_1(A_117, A_117, A_118)=k2_xboole_0(A_117, A_118) | ~r1_tarski(A_118, A_117))), inference(resolution, [status(thm)], [c_51, c_626])).
% 4.07/1.75  tff(c_643, plain, (k4_subset_1('#skF_2', '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_210, c_639])).
% 4.07/1.75  tff(c_652, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_533, c_643])).
% 4.07/1.75  tff(c_556, plain, (![A_110, B_111]: (k4_subset_1(u1_struct_0(A_110), B_111, k2_tops_1(A_110, B_111))=k2_pre_topc(A_110, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.07/1.75  tff(c_563, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_556])).
% 4.07/1.75  tff(c_571, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_563])).
% 4.07/1.75  tff(c_280, plain, (![A_79, B_80]: (m1_subset_1(k2_tops_1(A_79, B_80), k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.07/1.75  tff(c_22, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.07/1.75  tff(c_297, plain, (![A_79, B_80]: (r1_tarski(k2_tops_1(A_79, B_80), u1_struct_0(A_79)) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_280, c_22])).
% 4.07/1.75  tff(c_685, plain, (![A_123]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_123)=k2_xboole_0('#skF_2', A_123) | ~r1_tarski(A_123, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_38, c_626])).
% 4.07/1.75  tff(c_689, plain, (![B_80]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_80))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_80)) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_297, c_685])).
% 4.07/1.75  tff(c_1183, plain, (![B_160]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_160))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_160)) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_689])).
% 4.07/1.75  tff(c_1194, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_1183])).
% 4.07/1.75  tff(c_1204, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_652, c_571, c_1194])).
% 4.07/1.75  tff(c_1206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_469, c_1204])).
% 4.07/1.75  tff(c_1207, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.07/1.75  tff(c_1317, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1285, c_1207])).
% 4.07/1.75  tff(c_1208, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.07/1.75  tff(c_1296, plain, (![A_179, B_180]: (k2_pre_topc(A_179, B_180)=B_180 | ~v4_pre_topc(B_180, A_179) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.07/1.75  tff(c_1303, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1296])).
% 4.07/1.75  tff(c_1311, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1208, c_1303])).
% 4.07/1.75  tff(c_1900, plain, (![A_255, B_256]: (k7_subset_1(u1_struct_0(A_255), k2_pre_topc(A_255, B_256), k1_tops_1(A_255, B_256))=k2_tops_1(A_255, B_256) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.07/1.75  tff(c_1909, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1311, c_1900])).
% 4.07/1.75  tff(c_1913, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1285, c_1909])).
% 4.07/1.75  tff(c_1915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1317, c_1913])).
% 4.07/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.75  
% 4.07/1.75  Inference rules
% 4.07/1.75  ----------------------
% 4.07/1.75  #Ref     : 0
% 4.07/1.75  #Sup     : 433
% 4.07/1.75  #Fact    : 0
% 4.07/1.75  #Define  : 0
% 4.07/1.75  #Split   : 1
% 4.07/1.75  #Chain   : 0
% 4.07/1.75  #Close   : 0
% 4.07/1.75  
% 4.07/1.75  Ordering : KBO
% 4.07/1.75  
% 4.07/1.75  Simplification rules
% 4.07/1.75  ----------------------
% 4.07/1.75  #Subsume      : 25
% 4.07/1.75  #Demod        : 232
% 4.07/1.75  #Tautology    : 230
% 4.07/1.75  #SimpNegUnit  : 5
% 4.07/1.75  #BackRed      : 6
% 4.07/1.75  
% 4.07/1.75  #Partial instantiations: 0
% 4.07/1.75  #Strategies tried      : 1
% 4.07/1.75  
% 4.07/1.75  Timing (in seconds)
% 4.07/1.75  ----------------------
% 4.07/1.75  Preprocessing        : 0.34
% 4.07/1.75  Parsing              : 0.18
% 4.07/1.75  CNF conversion       : 0.02
% 4.07/1.75  Main loop            : 0.64
% 4.07/1.75  Inferencing          : 0.24
% 4.07/1.75  Reduction            : 0.21
% 4.07/1.75  Demodulation         : 0.15
% 4.07/1.75  BG Simplification    : 0.03
% 4.07/1.75  Subsumption          : 0.11
% 4.07/1.75  Abstraction          : 0.04
% 4.07/1.75  MUC search           : 0.00
% 4.07/1.75  Cooper               : 0.00
% 4.07/1.75  Total                : 1.02
% 4.07/1.76  Index Insertion      : 0.00
% 4.07/1.76  Index Deletion       : 0.00
% 4.07/1.76  Index Matching       : 0.00
% 4.07/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
