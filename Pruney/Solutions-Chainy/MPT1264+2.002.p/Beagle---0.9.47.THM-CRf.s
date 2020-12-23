%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:38 EST 2020

% Result     : Theorem 9.86s
% Output     : CNFRefutation 9.98s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 270 expanded)
%              Number of leaves         :   34 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  152 ( 607 expanded)
%              Number of equality atoms :   55 ( 174 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

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

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_20,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_104,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,(
    ! [B_47,A_48] : k1_setfam_1(k2_tarski(B_47,A_48)) = k3_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_104])).

tff(c_28,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_126,plain,(
    ! [B_47,A_48] : k3_xboole_0(B_47,A_48) = k3_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_28])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_54,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_32,c_54])).

tff(c_96,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_92])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_98,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_48])).

tff(c_209,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,C_62) = k3_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_215,plain,(
    ! [B_61] : k9_subset_1(k2_struct_0('#skF_3'),B_61,'#skF_4') = k3_xboole_0(B_61,'#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_209])).

tff(c_40,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_97,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_40])).

tff(c_225,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_97])).

tff(c_226,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_4','#skF_5')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_225])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_99,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_44])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_399,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r2_hidden('#skF_1'(A_86,B_87,C_88),C_88)
      | r2_hidden('#skF_2'(A_86,B_87,C_88),C_88)
      | k3_xboole_0(A_86,B_87) = C_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_413,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_399])).

tff(c_442,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_2'(A_94,B_95,B_95),B_95)
      | k3_xboole_0(A_94,B_95) = B_95 ) ),
    inference(resolution,[status(thm)],[c_16,c_399])).

tff(c_24,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(C_15,A_12)
      | ~ r2_hidden(C_15,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_457,plain,(
    ! [A_94,B_95,A_12] :
      ( r2_hidden('#skF_2'(A_94,B_95,B_95),A_12)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_12))
      | k3_xboole_0(A_94,B_95) = B_95 ) ),
    inference(resolution,[status(thm)],[c_442,c_24])).

tff(c_345,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_hidden('#skF_1'(A_80,B_81,C_82),B_81)
      | r2_hidden('#skF_2'(A_80,B_81,C_82),C_82)
      | k3_xboole_0(A_80,B_81) = C_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4378,plain,(
    ! [A_367,B_368,C_369,A_370] :
      ( r2_hidden('#skF_2'(A_367,B_368,C_369),A_370)
      | ~ m1_subset_1(C_369,k1_zfmisc_1(A_370))
      | r2_hidden('#skF_1'(A_367,B_368,C_369),B_368)
      | k3_xboole_0(A_367,B_368) = C_369 ) ),
    inference(resolution,[status(thm)],[c_345,c_24])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10072,plain,(
    ! [A_771,B_772,C_773] :
      ( ~ r2_hidden('#skF_2'(A_771,B_772,C_773),B_772)
      | ~ m1_subset_1(C_773,k1_zfmisc_1(A_771))
      | r2_hidden('#skF_1'(A_771,B_772,C_773),B_772)
      | k3_xboole_0(A_771,B_772) = C_773 ) ),
    inference(resolution,[status(thm)],[c_4378,c_10])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10738,plain,(
    ! [A_794,B_795] :
      ( ~ r2_hidden('#skF_2'(A_794,B_795,B_795),A_794)
      | ~ r2_hidden('#skF_2'(A_794,B_795,B_795),B_795)
      | ~ m1_subset_1(B_795,k1_zfmisc_1(A_794))
      | k3_xboole_0(A_794,B_795) = B_795 ) ),
    inference(resolution,[status(thm)],[c_10072,c_8])).

tff(c_10900,plain,(
    ! [A_796,B_797] :
      ( ~ r2_hidden('#skF_2'(A_796,B_797,B_797),B_797)
      | ~ m1_subset_1(B_797,k1_zfmisc_1(A_796))
      | k3_xboole_0(A_796,B_797) = B_797 ) ),
    inference(resolution,[status(thm)],[c_457,c_10738])).

tff(c_11067,plain,(
    ! [B_798,A_799] :
      ( ~ m1_subset_1(B_798,k1_zfmisc_1(A_799))
      | k3_xboole_0(A_799,B_798) = B_798 ) ),
    inference(resolution,[status(thm)],[c_413,c_10900])).

tff(c_11082,plain,(
    k3_xboole_0(k2_struct_0('#skF_3'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_99,c_11067])).

tff(c_11301,plain,(
    k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_11082,c_126])).

tff(c_46,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_299,plain,(
    ! [A_70,B_71] :
      ( k2_pre_topc(A_70,B_71) = k2_struct_0(A_70)
      | ~ v1_tops_1(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_302,plain,(
    ! [B_71] :
      ( k2_pre_topc('#skF_3',B_71) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_71,'#skF_3')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_299])).

tff(c_305,plain,(
    ! [B_72] :
      ( k2_pre_topc('#skF_3',B_72) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_72,'#skF_3')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_302])).

tff(c_311,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_305])).

tff(c_315,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_311])).

tff(c_42,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_214,plain,(
    ! [B_61] : k9_subset_1(k2_struct_0('#skF_3'),B_61,'#skF_5') = k3_xboole_0(B_61,'#skF_5') ),
    inference(resolution,[status(thm)],[c_99,c_209])).

tff(c_236,plain,(
    ! [A_65,C_66,B_67] :
      ( k9_subset_1(A_65,C_66,B_67) = k9_subset_1(A_65,B_67,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_238,plain,(
    ! [B_67] : k9_subset_1(k2_struct_0('#skF_3'),B_67,'#skF_5') = k9_subset_1(k2_struct_0('#skF_3'),'#skF_5',B_67) ),
    inference(resolution,[status(thm)],[c_99,c_236])).

tff(c_242,plain,(
    ! [B_67] : k9_subset_1(k2_struct_0('#skF_3'),'#skF_5',B_67) = k3_xboole_0(B_67,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_238])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_637,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_pre_topc(A_114,k9_subset_1(u1_struct_0(A_114),B_115,k2_pre_topc(A_114,C_116))) = k2_pre_topc(A_114,k9_subset_1(u1_struct_0(A_114),B_115,C_116))
      | ~ v3_pre_topc(B_115,A_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_655,plain,(
    ! [B_115,C_116] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_115,k2_pre_topc('#skF_3',C_116))) = k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_115,C_116))
      | ~ v3_pre_topc(B_115,'#skF_3')
      | ~ m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_637])).

tff(c_757,plain,(
    ! [B_140,C_141] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_140,k2_pre_topc('#skF_3',C_141))) = k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_140,C_141))
      | ~ v3_pre_topc(B_140,'#skF_3')
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_96,c_96,c_96,c_655])).

tff(c_787,plain,(
    ! [C_141] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),'#skF_5',C_141)) = k2_pre_topc('#skF_3',k3_xboole_0(k2_pre_topc('#skF_3',C_141),'#skF_5'))
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_757])).

tff(c_800,plain,(
    ! [C_142] :
      ( k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_pre_topc('#skF_3',C_142))) = k2_pre_topc('#skF_3',k3_xboole_0(C_142,'#skF_5'))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_42,c_242,c_126,c_787])).

tff(c_806,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_pre_topc('#skF_3','#skF_4'))) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_98,c_800])).

tff(c_810,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_806])).

tff(c_11658,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_4','#skF_5')) = k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11301,c_810])).

tff(c_11667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_11658])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.86/3.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/3.61  
% 9.98/3.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/3.62  %$ v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 9.98/3.62  
% 9.98/3.62  %Foreground sorts:
% 9.98/3.62  
% 9.98/3.62  
% 9.98/3.62  %Background operators:
% 9.98/3.62  
% 9.98/3.62  
% 9.98/3.62  %Foreground operators:
% 9.98/3.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.98/3.62  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.98/3.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.98/3.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.98/3.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.98/3.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.98/3.62  tff('#skF_5', type, '#skF_5': $i).
% 9.98/3.62  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 9.98/3.62  tff('#skF_3', type, '#skF_3': $i).
% 9.98/3.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.98/3.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.98/3.62  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.98/3.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.98/3.62  tff('#skF_4', type, '#skF_4': $i).
% 9.98/3.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.98/3.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.98/3.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.98/3.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.98/3.62  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.98/3.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.98/3.62  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.98/3.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.98/3.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.98/3.62  
% 9.98/3.63  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.98/3.63  tff(f_53, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.98/3.63  tff(f_101, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 9.98/3.63  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.98/3.63  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.98/3.63  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.98/3.63  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.98/3.63  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.98/3.63  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 9.98/3.63  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 9.98/3.63  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_1)).
% 9.98/3.63  tff(c_20, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.98/3.63  tff(c_104, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.98/3.63  tff(c_120, plain, (![B_47, A_48]: (k1_setfam_1(k2_tarski(B_47, A_48))=k3_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_20, c_104])).
% 9.98/3.63  tff(c_28, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.98/3.63  tff(c_126, plain, (![B_47, A_48]: (k3_xboole_0(B_47, A_48)=k3_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_120, c_28])).
% 9.98/3.63  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.98/3.63  tff(c_32, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.98/3.63  tff(c_54, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.98/3.63  tff(c_92, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_32, c_54])).
% 9.98/3.63  tff(c_96, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_92])).
% 9.98/3.63  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.98/3.63  tff(c_98, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_48])).
% 9.98/3.63  tff(c_209, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, C_62)=k3_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.98/3.63  tff(c_215, plain, (![B_61]: (k9_subset_1(k2_struct_0('#skF_3'), B_61, '#skF_4')=k3_xboole_0(B_61, '#skF_4'))), inference(resolution, [status(thm)], [c_98, c_209])).
% 9.98/3.63  tff(c_40, plain, (k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.98/3.63  tff(c_97, plain, (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_40])).
% 9.98/3.63  tff(c_225, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_97])).
% 9.98/3.63  tff(c_226, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_225])).
% 9.98/3.63  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.98/3.63  tff(c_99, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_44])).
% 9.98/3.63  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.98/3.63  tff(c_399, plain, (![A_86, B_87, C_88]: (~r2_hidden('#skF_1'(A_86, B_87, C_88), C_88) | r2_hidden('#skF_2'(A_86, B_87, C_88), C_88) | k3_xboole_0(A_86, B_87)=C_88)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.98/3.63  tff(c_413, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_399])).
% 9.98/3.63  tff(c_442, plain, (![A_94, B_95]: (r2_hidden('#skF_2'(A_94, B_95, B_95), B_95) | k3_xboole_0(A_94, B_95)=B_95)), inference(resolution, [status(thm)], [c_16, c_399])).
% 9.98/3.63  tff(c_24, plain, (![C_15, A_12, B_13]: (r2_hidden(C_15, A_12) | ~r2_hidden(C_15, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.98/3.63  tff(c_457, plain, (![A_94, B_95, A_12]: (r2_hidden('#skF_2'(A_94, B_95, B_95), A_12) | ~m1_subset_1(B_95, k1_zfmisc_1(A_12)) | k3_xboole_0(A_94, B_95)=B_95)), inference(resolution, [status(thm)], [c_442, c_24])).
% 9.98/3.63  tff(c_345, plain, (![A_80, B_81, C_82]: (r2_hidden('#skF_1'(A_80, B_81, C_82), B_81) | r2_hidden('#skF_2'(A_80, B_81, C_82), C_82) | k3_xboole_0(A_80, B_81)=C_82)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.98/3.63  tff(c_4378, plain, (![A_367, B_368, C_369, A_370]: (r2_hidden('#skF_2'(A_367, B_368, C_369), A_370) | ~m1_subset_1(C_369, k1_zfmisc_1(A_370)) | r2_hidden('#skF_1'(A_367, B_368, C_369), B_368) | k3_xboole_0(A_367, B_368)=C_369)), inference(resolution, [status(thm)], [c_345, c_24])).
% 9.98/3.63  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.98/3.63  tff(c_10072, plain, (![A_771, B_772, C_773]: (~r2_hidden('#skF_2'(A_771, B_772, C_773), B_772) | ~m1_subset_1(C_773, k1_zfmisc_1(A_771)) | r2_hidden('#skF_1'(A_771, B_772, C_773), B_772) | k3_xboole_0(A_771, B_772)=C_773)), inference(resolution, [status(thm)], [c_4378, c_10])).
% 9.98/3.63  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.98/3.63  tff(c_10738, plain, (![A_794, B_795]: (~r2_hidden('#skF_2'(A_794, B_795, B_795), A_794) | ~r2_hidden('#skF_2'(A_794, B_795, B_795), B_795) | ~m1_subset_1(B_795, k1_zfmisc_1(A_794)) | k3_xboole_0(A_794, B_795)=B_795)), inference(resolution, [status(thm)], [c_10072, c_8])).
% 9.98/3.63  tff(c_10900, plain, (![A_796, B_797]: (~r2_hidden('#skF_2'(A_796, B_797, B_797), B_797) | ~m1_subset_1(B_797, k1_zfmisc_1(A_796)) | k3_xboole_0(A_796, B_797)=B_797)), inference(resolution, [status(thm)], [c_457, c_10738])).
% 9.98/3.63  tff(c_11067, plain, (![B_798, A_799]: (~m1_subset_1(B_798, k1_zfmisc_1(A_799)) | k3_xboole_0(A_799, B_798)=B_798)), inference(resolution, [status(thm)], [c_413, c_10900])).
% 9.98/3.63  tff(c_11082, plain, (k3_xboole_0(k2_struct_0('#skF_3'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_99, c_11067])).
% 9.98/3.63  tff(c_11301, plain, (k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_11082, c_126])).
% 9.98/3.63  tff(c_46, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.98/3.63  tff(c_299, plain, (![A_70, B_71]: (k2_pre_topc(A_70, B_71)=k2_struct_0(A_70) | ~v1_tops_1(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.98/3.63  tff(c_302, plain, (![B_71]: (k2_pre_topc('#skF_3', B_71)=k2_struct_0('#skF_3') | ~v1_tops_1(B_71, '#skF_3') | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_299])).
% 9.98/3.63  tff(c_305, plain, (![B_72]: (k2_pre_topc('#skF_3', B_72)=k2_struct_0('#skF_3') | ~v1_tops_1(B_72, '#skF_3') | ~m1_subset_1(B_72, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_302])).
% 9.98/3.63  tff(c_311, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_98, c_305])).
% 9.98/3.63  tff(c_315, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_311])).
% 9.98/3.63  tff(c_42, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.98/3.63  tff(c_214, plain, (![B_61]: (k9_subset_1(k2_struct_0('#skF_3'), B_61, '#skF_5')=k3_xboole_0(B_61, '#skF_5'))), inference(resolution, [status(thm)], [c_99, c_209])).
% 9.98/3.63  tff(c_236, plain, (![A_65, C_66, B_67]: (k9_subset_1(A_65, C_66, B_67)=k9_subset_1(A_65, B_67, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.98/3.63  tff(c_238, plain, (![B_67]: (k9_subset_1(k2_struct_0('#skF_3'), B_67, '#skF_5')=k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', B_67))), inference(resolution, [status(thm)], [c_99, c_236])).
% 9.98/3.63  tff(c_242, plain, (![B_67]: (k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', B_67)=k3_xboole_0(B_67, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_238])).
% 9.98/3.63  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.98/3.63  tff(c_637, plain, (![A_114, B_115, C_116]: (k2_pre_topc(A_114, k9_subset_1(u1_struct_0(A_114), B_115, k2_pre_topc(A_114, C_116)))=k2_pre_topc(A_114, k9_subset_1(u1_struct_0(A_114), B_115, C_116)) | ~v3_pre_topc(B_115, A_114) | ~m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(A_114))) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.98/3.63  tff(c_655, plain, (![B_115, C_116]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_115, k2_pre_topc('#skF_3', C_116)))=k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_115, C_116)) | ~v3_pre_topc(B_115, '#skF_3') | ~m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_637])).
% 9.98/3.63  tff(c_757, plain, (![B_140, C_141]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_140, k2_pre_topc('#skF_3', C_141)))=k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_140, C_141)) | ~v3_pre_topc(B_140, '#skF_3') | ~m1_subset_1(C_141, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_140, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_96, c_96, c_96, c_655])).
% 9.98/3.63  tff(c_787, plain, (![C_141]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', C_141))=k2_pre_topc('#skF_3', k3_xboole_0(k2_pre_topc('#skF_3', C_141), '#skF_5')) | ~v3_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1(C_141, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_242, c_757])).
% 9.98/3.63  tff(c_800, plain, (![C_142]: (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_pre_topc('#skF_3', C_142)))=k2_pre_topc('#skF_3', k3_xboole_0(C_142, '#skF_5')) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_42, c_242, c_126, c_787])).
% 9.98/3.63  tff(c_806, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_pre_topc('#skF_3', '#skF_4')))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_98, c_800])).
% 9.98/3.63  tff(c_810, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_806])).
% 9.98/3.63  tff(c_11658, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11301, c_810])).
% 9.98/3.63  tff(c_11667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_11658])).
% 9.98/3.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/3.63  
% 9.98/3.63  Inference rules
% 9.98/3.63  ----------------------
% 9.98/3.63  #Ref     : 0
% 9.98/3.63  #Sup     : 2797
% 9.98/3.63  #Fact    : 0
% 9.98/3.63  #Define  : 0
% 9.98/3.63  #Split   : 8
% 9.98/3.63  #Chain   : 0
% 9.98/3.63  #Close   : 0
% 9.98/3.63  
% 9.98/3.63  Ordering : KBO
% 9.98/3.63  
% 9.98/3.63  Simplification rules
% 9.98/3.63  ----------------------
% 9.98/3.63  #Subsume      : 702
% 9.98/3.63  #Demod        : 1807
% 9.98/3.63  #Tautology    : 307
% 9.98/3.63  #SimpNegUnit  : 4
% 9.98/3.63  #BackRed      : 22
% 9.98/3.63  
% 9.98/3.63  #Partial instantiations: 0
% 9.98/3.63  #Strategies tried      : 1
% 9.98/3.63  
% 9.98/3.63  Timing (in seconds)
% 9.98/3.63  ----------------------
% 9.98/3.64  Preprocessing        : 0.33
% 9.98/3.64  Parsing              : 0.17
% 9.98/3.64  CNF conversion       : 0.02
% 9.98/3.64  Main loop            : 2.54
% 9.98/3.64  Inferencing          : 0.70
% 9.98/3.64  Reduction            : 0.83
% 9.98/3.64  Demodulation         : 0.65
% 9.98/3.64  BG Simplification    : 0.09
% 9.98/3.64  Subsumption          : 0.77
% 9.98/3.64  Abstraction          : 0.13
% 9.98/3.64  MUC search           : 0.00
% 9.98/3.64  Cooper               : 0.00
% 9.98/3.64  Total                : 2.91
% 9.98/3.64  Index Insertion      : 0.00
% 9.98/3.64  Index Deletion       : 0.00
% 9.98/3.64  Index Matching       : 0.00
% 9.98/3.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
