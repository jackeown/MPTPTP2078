%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:23 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 370 expanded)
%              Number of leaves         :   41 ( 141 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 ( 666 expanded)
%              Number of equality atoms :   55 ( 159 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_74,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    ! [A_37] :
      ( l1_struct_0(A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_96,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_101,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_38,c_96])).

tff(c_105,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_101])).

tff(c_44,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_111,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_44])).

tff(c_112,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_106,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_40])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_201,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_50])).

tff(c_202,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_201])).

tff(c_291,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(A_73,B_74) = k3_subset_1(A_73,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_298,plain,(
    k4_xboole_0(k2_struct_0('#skF_2'),'#skF_3') = k3_subset_1(k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_291])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_287,plain,(
    ! [C_70,A_71,B_72] :
      ( r2_hidden(C_70,A_71)
      | ~ r2_hidden(C_70,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_493,plain,(
    ! [A_97,B_98,A_99] :
      ( r2_hidden('#skF_1'(A_97,B_98),A_99)
      | ~ m1_subset_1(A_97,k1_zfmisc_1(A_99))
      | r1_tarski(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_6,c_287])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_506,plain,(
    ! [A_101,A_102] :
      ( ~ m1_subset_1(A_101,k1_zfmisc_1(A_102))
      | r1_tarski(A_101,A_102) ) ),
    inference(resolution,[status(thm)],[c_493,c_4])).

tff(c_517,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_106,c_506])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_523,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_517,c_10])).

tff(c_14,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_114,plain,(
    ! [A_48,B_49] : k1_setfam_1(k2_tarski(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_129,plain,(
    ! [B_50,A_51] : k1_setfam_1(k2_tarski(B_50,A_51)) = k3_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_114])).

tff(c_30,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_135,plain,(
    ! [B_50,A_51] : k3_xboole_0(B_50,A_51) = k3_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_30])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_204,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_374,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,k4_xboole_0(A_82,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_204])).

tff(c_395,plain,(
    ! [B_50,A_51] : k4_xboole_0(B_50,k3_xboole_0(A_51,B_50)) = k3_xboole_0(B_50,k4_xboole_0(B_50,A_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_374])).

tff(c_528,plain,(
    k3_xboole_0(k2_struct_0('#skF_2'),k4_xboole_0(k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0(k2_struct_0('#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_395])).

tff(c_540,plain,(
    k3_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k3_subset_1(k2_struct_0('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_298,c_528])).

tff(c_16,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [A_17] : m1_subset_1(k2_subset_1(A_17),k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_51,plain,(
    ! [A_17] : m1_subset_1(A_17,k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k3_subset_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_447,plain,(
    ! [A_86,B_87,C_88] :
      ( k9_subset_1(A_86,B_87,C_88) = k3_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1282,plain,(
    ! [A_138,B_139,B_140] :
      ( k9_subset_1(A_138,B_139,k3_subset_1(A_138,B_140)) = k3_xboole_0(B_139,k3_subset_1(A_138,B_140))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_138)) ) ),
    inference(resolution,[status(thm)],[c_22,c_447])).

tff(c_1294,plain,(
    ! [B_139] : k9_subset_1(k2_struct_0('#skF_2'),B_139,k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k3_xboole_0(B_139,k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_106,c_1282])).

tff(c_561,plain,(
    ! [A_103,B_104,C_105] :
      ( k9_subset_1(A_103,B_104,k3_subset_1(A_103,C_105)) = k7_subset_1(A_103,B_104,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_569,plain,(
    ! [B_104] :
      ( k9_subset_1(k2_struct_0('#skF_2'),B_104,k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k7_subset_1(k2_struct_0('#skF_2'),B_104,'#skF_3')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_106,c_561])).

tff(c_2256,plain,(
    ! [B_184] :
      ( k3_xboole_0(B_184,k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k7_subset_1(k2_struct_0('#skF_2'),B_184,'#skF_3')
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_569])).

tff(c_2267,plain,(
    k3_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_2256])).

tff(c_2271,plain,(
    k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),'#skF_3') = k3_subset_1(k2_struct_0('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_2267])).

tff(c_466,plain,(
    ! [B_91,A_92] :
      ( v4_pre_topc(B_91,A_92)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_92),k2_struct_0(A_92),B_91),A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_469,plain,(
    ! [B_91] :
      ( v4_pre_topc(B_91,'#skF_2')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),B_91),'#skF_2')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_466])).

tff(c_471,plain,(
    ! [B_91] :
      ( v4_pre_topc(B_91,'#skF_2')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),B_91),'#skF_2')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_105,c_469])).

tff(c_2278,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2271,c_471])).

tff(c_2284,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_202,c_2278])).

tff(c_2286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_2284])).

tff(c_2287,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_2288,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_2463,plain,(
    ! [A_209,B_210] :
      ( k4_xboole_0(A_209,B_210) = k3_subset_1(A_209,B_210)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(A_209)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2470,plain,(
    k4_xboole_0(k2_struct_0('#skF_2'),'#skF_3') = k3_subset_1(k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_2463])).

tff(c_2553,plain,(
    ! [C_218,A_219,B_220] :
      ( r2_hidden(C_218,A_219)
      | ~ r2_hidden(C_218,B_220)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(A_219)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2678,plain,(
    ! [A_234,B_235,A_236] :
      ( r2_hidden('#skF_1'(A_234,B_235),A_236)
      | ~ m1_subset_1(A_234,k1_zfmisc_1(A_236))
      | r1_tarski(A_234,B_235) ) ),
    inference(resolution,[status(thm)],[c_6,c_2553])).

tff(c_2690,plain,(
    ! [A_237,A_238] :
      ( ~ m1_subset_1(A_237,k1_zfmisc_1(A_238))
      | r1_tarski(A_237,A_238) ) ),
    inference(resolution,[status(thm)],[c_2678,c_4])).

tff(c_2701,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_106,c_2690])).

tff(c_2707,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2701,c_10])).

tff(c_2290,plain,(
    ! [A_187,B_188] : k1_setfam_1(k2_tarski(A_187,B_188)) = k3_xboole_0(A_187,B_188) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2305,plain,(
    ! [B_189,A_190] : k1_setfam_1(k2_tarski(B_189,A_190)) = k3_xboole_0(A_190,B_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2290])).

tff(c_2311,plain,(
    ! [B_189,A_190] : k3_xboole_0(B_189,A_190) = k3_xboole_0(A_190,B_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_2305,c_30])).

tff(c_2516,plain,(
    k4_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k3_xboole_0(k2_struct_0('#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2470,c_12])).

tff(c_2519,plain,(
    k4_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k3_xboole_0('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_2516])).

tff(c_2549,plain,(
    k4_xboole_0(k2_struct_0('#skF_2'),k3_xboole_0('#skF_3',k2_struct_0('#skF_2'))) = k3_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2519,c_12])).

tff(c_2708,plain,(
    k3_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0(k2_struct_0('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2707,c_2549])).

tff(c_2710,plain,(
    k3_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k3_subset_1(k2_struct_0('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2470,c_2708])).

tff(c_2623,plain,(
    ! [A_225,B_226,C_227] :
      ( k9_subset_1(A_225,B_226,C_227) = k3_xboole_0(B_226,C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(A_225)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3719,plain,(
    ! [A_286,B_287,B_288] :
      ( k9_subset_1(A_286,B_287,k3_subset_1(A_286,B_288)) = k3_xboole_0(B_287,k3_subset_1(A_286,B_288))
      | ~ m1_subset_1(B_288,k1_zfmisc_1(A_286)) ) ),
    inference(resolution,[status(thm)],[c_22,c_2623])).

tff(c_3731,plain,(
    ! [B_287] : k9_subset_1(k2_struct_0('#skF_2'),B_287,k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k3_xboole_0(B_287,k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_106,c_3719])).

tff(c_2739,plain,(
    ! [A_239,B_240,C_241] :
      ( k9_subset_1(A_239,B_240,k3_subset_1(A_239,C_241)) = k7_subset_1(A_239,B_240,C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(A_239))
      | ~ m1_subset_1(B_240,k1_zfmisc_1(A_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2747,plain,(
    ! [B_240] :
      ( k9_subset_1(k2_struct_0('#skF_2'),B_240,k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k7_subset_1(k2_struct_0('#skF_2'),B_240,'#skF_3')
      | ~ m1_subset_1(B_240,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_106,c_2739])).

tff(c_4230,plain,(
    ! [B_299] :
      ( k3_xboole_0(B_299,k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k7_subset_1(k2_struct_0('#skF_2'),B_299,'#skF_3')
      | ~ m1_subset_1(B_299,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3731,c_2747])).

tff(c_4241,plain,(
    k3_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_4230])).

tff(c_4245,plain,(
    k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),'#skF_3') = k3_subset_1(k2_struct_0('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2710,c_4241])).

tff(c_2802,plain,(
    ! [A_245,B_246] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_245),k2_struct_0(A_245),B_246),A_245)
      | ~ v4_pre_topc(B_246,A_245)
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2805,plain,(
    ! [B_246] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),B_246),'#skF_2')
      | ~ v4_pre_topc(B_246,'#skF_2')
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_2802])).

tff(c_2807,plain,(
    ! [B_246] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),B_246),'#skF_2')
      | ~ v4_pre_topc(B_246,'#skF_2')
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_105,c_2805])).

tff(c_4252,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4245,c_2807])).

tff(c_4258,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2288,c_4252])).

tff(c_4260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2287,c_4258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/2.02  
% 5.29/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/2.02  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 5.29/2.02  
% 5.29/2.02  %Foreground sorts:
% 5.29/2.02  
% 5.29/2.02  
% 5.29/2.02  %Background operators:
% 5.29/2.02  
% 5.29/2.02  
% 5.29/2.02  %Foreground operators:
% 5.29/2.02  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.29/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.29/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.29/2.02  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.29/2.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.29/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.29/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.29/2.02  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.29/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.29/2.02  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.29/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.29/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.29/2.02  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.29/2.02  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.29/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.29/2.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.29/2.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.29/2.02  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.29/2.02  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.29/2.02  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.29/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.29/2.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.29/2.02  
% 5.29/2.04  tff(f_101, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 5.29/2.04  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.29/2.04  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.29/2.04  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.29/2.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.29/2.04  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.29/2.04  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.29/2.04  tff(f_42, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.29/2.04  tff(f_74, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.29/2.04  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.29/2.04  tff(f_44, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.29/2.04  tff(f_50, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.29/2.04  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.29/2.04  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.29/2.04  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 5.29/2.04  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 5.29/2.04  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.29/2.04  tff(c_38, plain, (![A_37]: (l1_struct_0(A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.29/2.04  tff(c_96, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.29/2.04  tff(c_101, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_38, c_96])).
% 5.29/2.04  tff(c_105, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_101])).
% 5.29/2.04  tff(c_44, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.29/2.04  tff(c_111, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_44])).
% 5.29/2.04  tff(c_112, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_111])).
% 5.29/2.04  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.29/2.04  tff(c_106, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_40])).
% 5.29/2.04  tff(c_50, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.29/2.04  tff(c_201, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_50])).
% 5.29/2.04  tff(c_202, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_112, c_201])).
% 5.29/2.04  tff(c_291, plain, (![A_73, B_74]: (k4_xboole_0(A_73, B_74)=k3_subset_1(A_73, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.29/2.04  tff(c_298, plain, (k4_xboole_0(k2_struct_0('#skF_2'), '#skF_3')=k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_106, c_291])).
% 5.29/2.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.29/2.04  tff(c_287, plain, (![C_70, A_71, B_72]: (r2_hidden(C_70, A_71) | ~r2_hidden(C_70, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.29/2.04  tff(c_493, plain, (![A_97, B_98, A_99]: (r2_hidden('#skF_1'(A_97, B_98), A_99) | ~m1_subset_1(A_97, k1_zfmisc_1(A_99)) | r1_tarski(A_97, B_98))), inference(resolution, [status(thm)], [c_6, c_287])).
% 5.29/2.04  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.29/2.04  tff(c_506, plain, (![A_101, A_102]: (~m1_subset_1(A_101, k1_zfmisc_1(A_102)) | r1_tarski(A_101, A_102))), inference(resolution, [status(thm)], [c_493, c_4])).
% 5.29/2.04  tff(c_517, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_106, c_506])).
% 5.29/2.04  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.29/2.04  tff(c_523, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_517, c_10])).
% 5.29/2.04  tff(c_14, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.29/2.04  tff(c_114, plain, (![A_48, B_49]: (k1_setfam_1(k2_tarski(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.29/2.04  tff(c_129, plain, (![B_50, A_51]: (k1_setfam_1(k2_tarski(B_50, A_51))=k3_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_14, c_114])).
% 5.29/2.04  tff(c_30, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.29/2.04  tff(c_135, plain, (![B_50, A_51]: (k3_xboole_0(B_50, A_51)=k3_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_129, c_30])).
% 5.29/2.04  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.29/2.04  tff(c_204, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.29/2.04  tff(c_374, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k3_xboole_0(A_82, k4_xboole_0(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_204])).
% 5.29/2.04  tff(c_395, plain, (![B_50, A_51]: (k4_xboole_0(B_50, k3_xboole_0(A_51, B_50))=k3_xboole_0(B_50, k4_xboole_0(B_50, A_51)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_374])).
% 5.29/2.04  tff(c_528, plain, (k3_xboole_0(k2_struct_0('#skF_2'), k4_xboole_0(k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0(k2_struct_0('#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_523, c_395])).
% 5.29/2.04  tff(c_540, plain, (k3_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_298, c_528])).
% 5.29/2.04  tff(c_16, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.29/2.04  tff(c_20, plain, (![A_17]: (m1_subset_1(k2_subset_1(A_17), k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.29/2.04  tff(c_51, plain, (![A_17]: (m1_subset_1(A_17, k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 5.29/2.04  tff(c_22, plain, (![A_18, B_19]: (m1_subset_1(k3_subset_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.29/2.04  tff(c_447, plain, (![A_86, B_87, C_88]: (k9_subset_1(A_86, B_87, C_88)=k3_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.29/2.04  tff(c_1282, plain, (![A_138, B_139, B_140]: (k9_subset_1(A_138, B_139, k3_subset_1(A_138, B_140))=k3_xboole_0(B_139, k3_subset_1(A_138, B_140)) | ~m1_subset_1(B_140, k1_zfmisc_1(A_138)))), inference(resolution, [status(thm)], [c_22, c_447])).
% 5.29/2.04  tff(c_1294, plain, (![B_139]: (k9_subset_1(k2_struct_0('#skF_2'), B_139, k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k3_xboole_0(B_139, k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')))), inference(resolution, [status(thm)], [c_106, c_1282])).
% 5.29/2.04  tff(c_561, plain, (![A_103, B_104, C_105]: (k9_subset_1(A_103, B_104, k3_subset_1(A_103, C_105))=k7_subset_1(A_103, B_104, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.29/2.04  tff(c_569, plain, (![B_104]: (k9_subset_1(k2_struct_0('#skF_2'), B_104, k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k7_subset_1(k2_struct_0('#skF_2'), B_104, '#skF_3') | ~m1_subset_1(B_104, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_106, c_561])).
% 5.29/2.04  tff(c_2256, plain, (![B_184]: (k3_xboole_0(B_184, k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k7_subset_1(k2_struct_0('#skF_2'), B_184, '#skF_3') | ~m1_subset_1(B_184, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_569])).
% 5.29/2.04  tff(c_2267, plain, (k3_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_51, c_2256])).
% 5.29/2.04  tff(c_2271, plain, (k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), '#skF_3')=k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_540, c_2267])).
% 5.29/2.04  tff(c_466, plain, (![B_91, A_92]: (v4_pre_topc(B_91, A_92) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_92), k2_struct_0(A_92), B_91), A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.29/2.04  tff(c_469, plain, (![B_91]: (v4_pre_topc(B_91, '#skF_2') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), B_91), '#skF_2') | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_466])).
% 5.29/2.04  tff(c_471, plain, (![B_91]: (v4_pre_topc(B_91, '#skF_2') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), B_91), '#skF_2') | ~m1_subset_1(B_91, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_105, c_469])).
% 5.29/2.04  tff(c_2278, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2271, c_471])).
% 5.29/2.04  tff(c_2284, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_202, c_2278])).
% 5.29/2.04  tff(c_2286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_2284])).
% 5.29/2.04  tff(c_2287, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_111])).
% 5.29/2.04  tff(c_2288, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_111])).
% 5.29/2.04  tff(c_2463, plain, (![A_209, B_210]: (k4_xboole_0(A_209, B_210)=k3_subset_1(A_209, B_210) | ~m1_subset_1(B_210, k1_zfmisc_1(A_209)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.29/2.04  tff(c_2470, plain, (k4_xboole_0(k2_struct_0('#skF_2'), '#skF_3')=k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_106, c_2463])).
% 5.29/2.04  tff(c_2553, plain, (![C_218, A_219, B_220]: (r2_hidden(C_218, A_219) | ~r2_hidden(C_218, B_220) | ~m1_subset_1(B_220, k1_zfmisc_1(A_219)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.29/2.04  tff(c_2678, plain, (![A_234, B_235, A_236]: (r2_hidden('#skF_1'(A_234, B_235), A_236) | ~m1_subset_1(A_234, k1_zfmisc_1(A_236)) | r1_tarski(A_234, B_235))), inference(resolution, [status(thm)], [c_6, c_2553])).
% 5.29/2.04  tff(c_2690, plain, (![A_237, A_238]: (~m1_subset_1(A_237, k1_zfmisc_1(A_238)) | r1_tarski(A_237, A_238))), inference(resolution, [status(thm)], [c_2678, c_4])).
% 5.29/2.04  tff(c_2701, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_106, c_2690])).
% 5.29/2.04  tff(c_2707, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_2701, c_10])).
% 5.29/2.04  tff(c_2290, plain, (![A_187, B_188]: (k1_setfam_1(k2_tarski(A_187, B_188))=k3_xboole_0(A_187, B_188))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.29/2.04  tff(c_2305, plain, (![B_189, A_190]: (k1_setfam_1(k2_tarski(B_189, A_190))=k3_xboole_0(A_190, B_189))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2290])).
% 5.29/2.04  tff(c_2311, plain, (![B_189, A_190]: (k3_xboole_0(B_189, A_190)=k3_xboole_0(A_190, B_189))), inference(superposition, [status(thm), theory('equality')], [c_2305, c_30])).
% 5.29/2.04  tff(c_2516, plain, (k4_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k3_xboole_0(k2_struct_0('#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2470, c_12])).
% 5.29/2.04  tff(c_2519, plain, (k4_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k3_xboole_0('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_2516])).
% 5.29/2.04  tff(c_2549, plain, (k4_xboole_0(k2_struct_0('#skF_2'), k3_xboole_0('#skF_3', k2_struct_0('#skF_2')))=k3_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2519, c_12])).
% 5.29/2.04  tff(c_2708, plain, (k3_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0(k2_struct_0('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2707, c_2549])).
% 5.29/2.04  tff(c_2710, plain, (k3_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2470, c_2708])).
% 5.29/2.04  tff(c_2623, plain, (![A_225, B_226, C_227]: (k9_subset_1(A_225, B_226, C_227)=k3_xboole_0(B_226, C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(A_225)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.29/2.04  tff(c_3719, plain, (![A_286, B_287, B_288]: (k9_subset_1(A_286, B_287, k3_subset_1(A_286, B_288))=k3_xboole_0(B_287, k3_subset_1(A_286, B_288)) | ~m1_subset_1(B_288, k1_zfmisc_1(A_286)))), inference(resolution, [status(thm)], [c_22, c_2623])).
% 5.29/2.04  tff(c_3731, plain, (![B_287]: (k9_subset_1(k2_struct_0('#skF_2'), B_287, k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k3_xboole_0(B_287, k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')))), inference(resolution, [status(thm)], [c_106, c_3719])).
% 5.29/2.04  tff(c_2739, plain, (![A_239, B_240, C_241]: (k9_subset_1(A_239, B_240, k3_subset_1(A_239, C_241))=k7_subset_1(A_239, B_240, C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(A_239)) | ~m1_subset_1(B_240, k1_zfmisc_1(A_239)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.29/2.04  tff(c_2747, plain, (![B_240]: (k9_subset_1(k2_struct_0('#skF_2'), B_240, k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k7_subset_1(k2_struct_0('#skF_2'), B_240, '#skF_3') | ~m1_subset_1(B_240, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_106, c_2739])).
% 5.29/2.04  tff(c_4230, plain, (![B_299]: (k3_xboole_0(B_299, k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k7_subset_1(k2_struct_0('#skF_2'), B_299, '#skF_3') | ~m1_subset_1(B_299, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_3731, c_2747])).
% 5.29/2.04  tff(c_4241, plain, (k3_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_51, c_4230])).
% 5.29/2.04  tff(c_4245, plain, (k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), '#skF_3')=k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2710, c_4241])).
% 5.29/2.04  tff(c_2802, plain, (![A_245, B_246]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_245), k2_struct_0(A_245), B_246), A_245) | ~v4_pre_topc(B_246, A_245) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.29/2.04  tff(c_2805, plain, (![B_246]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), B_246), '#skF_2') | ~v4_pre_topc(B_246, '#skF_2') | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_2802])).
% 5.29/2.04  tff(c_2807, plain, (![B_246]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), B_246), '#skF_2') | ~v4_pre_topc(B_246, '#skF_2') | ~m1_subset_1(B_246, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_105, c_2805])).
% 5.29/2.04  tff(c_4252, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4245, c_2807])).
% 5.29/2.04  tff(c_4258, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2288, c_4252])).
% 5.29/2.04  tff(c_4260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2287, c_4258])).
% 5.29/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/2.04  
% 5.29/2.04  Inference rules
% 5.29/2.04  ----------------------
% 5.29/2.04  #Ref     : 0
% 5.29/2.04  #Sup     : 1044
% 5.29/2.04  #Fact    : 0
% 5.29/2.04  #Define  : 0
% 5.29/2.04  #Split   : 2
% 5.29/2.04  #Chain   : 0
% 5.29/2.04  #Close   : 0
% 5.29/2.04  
% 5.29/2.04  Ordering : KBO
% 5.29/2.04  
% 5.29/2.04  Simplification rules
% 5.29/2.04  ----------------------
% 5.29/2.04  #Subsume      : 54
% 5.29/2.04  #Demod        : 782
% 5.29/2.04  #Tautology    : 528
% 5.29/2.04  #SimpNegUnit  : 5
% 5.29/2.04  #BackRed      : 10
% 5.29/2.04  
% 5.29/2.04  #Partial instantiations: 0
% 5.29/2.04  #Strategies tried      : 1
% 5.29/2.04  
% 5.29/2.04  Timing (in seconds)
% 5.29/2.04  ----------------------
% 5.29/2.04  Preprocessing        : 0.31
% 5.29/2.04  Parsing              : 0.16
% 5.29/2.04  CNF conversion       : 0.02
% 5.29/2.04  Main loop            : 0.92
% 5.29/2.04  Inferencing          : 0.30
% 5.29/2.04  Reduction            : 0.38
% 5.29/2.04  Demodulation         : 0.30
% 5.29/2.04  BG Simplification    : 0.04
% 5.29/2.04  Subsumption          : 0.15
% 5.29/2.04  Abstraction          : 0.05
% 5.29/2.04  MUC search           : 0.00
% 5.29/2.04  Cooper               : 0.00
% 5.29/2.04  Total                : 1.27
% 5.29/2.04  Index Insertion      : 0.00
% 5.29/2.04  Index Deletion       : 0.00
% 5.29/2.04  Index Matching       : 0.00
% 5.29/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
