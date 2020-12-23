%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:27 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 655 expanded)
%              Number of leaves         :   40 ( 235 expanded)
%              Depth                    :   16
%              Number of atoms          :  179 (1386 expanded)
%              Number of equality atoms :   69 ( 372 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

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

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_111,axiom,(
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

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2255,plain,(
    ! [A_166,B_167] :
      ( r1_tarski(k1_tops_1(A_166,B_167),B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2263,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2255])).

tff(c_2268,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2263])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2031,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(A_147,B_148) = k3_subset_1(A_147,B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2038,plain,(
    ! [B_23,A_22] :
      ( k4_xboole_0(B_23,A_22) = k3_subset_1(B_23,A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_2031])).

tff(c_2275,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2268,c_2038])).

tff(c_2227,plain,(
    ! [A_159,B_160,C_161] :
      ( k7_subset_1(A_159,B_160,C_161) = k4_xboole_0(B_160,C_161)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(A_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2236,plain,(
    ! [C_161] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_161) = k4_xboole_0('#skF_2',C_161) ),
    inference(resolution,[status(thm)],[c_40,c_2227])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_115,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1008,plain,(
    ! [B_105,A_106] :
      ( v4_pre_topc(B_105,A_106)
      | k2_pre_topc(A_106,B_105) != B_105
      | ~ v2_pre_topc(A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1022,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1008])).

tff(c_1028,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1022])).

tff(c_1029,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_1028])).

tff(c_544,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_tops_1(A_74,B_75),B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_552,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_544])).

tff(c_557,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_552])).

tff(c_514,plain,(
    ! [A_70,B_71,C_72] :
      ( k7_subset_1(A_70,B_71,C_72) = k4_xboole_0(B_71,C_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_524,plain,(
    ! [C_73] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_73) = k4_xboole_0('#skF_2',C_73) ),
    inference(resolution,[status(thm)],[c_40,c_514])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_213,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_52])).

tff(c_530,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_213])).

tff(c_196,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_207,plain,(
    ! [B_23,A_22] :
      ( k4_xboole_0(B_23,A_22) = k3_subset_1(B_23,A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_196])).

tff(c_560,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_557,c_207])).

tff(c_562,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_560])).

tff(c_190,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k3_subset_1(A_56,B_57),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_194,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k3_subset_1(A_56,B_57),A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_190,c_22])).

tff(c_566,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_194])).

tff(c_660,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_663,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_660])).

tff(c_667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_663])).

tff(c_668,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_669,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_934,plain,(
    ! [A_95,B_96,C_97] :
      ( k4_subset_1(A_95,B_96,C_97) = k2_xboole_0(B_96,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1105,plain,(
    ! [B_112,B_113,A_114] :
      ( k4_subset_1(B_112,B_113,A_114) = k2_xboole_0(B_113,A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(B_112))
      | ~ r1_tarski(A_114,B_112) ) ),
    inference(resolution,[status(thm)],[c_24,c_934])).

tff(c_1196,plain,(
    ! [A_122] :
      ( k4_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2'),A_122) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),A_122)
      | ~ r1_tarski(A_122,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_669,c_1105])).

tff(c_8,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( k4_subset_1(A_18,B_19,k3_subset_1(A_18,B_19)) = k2_subset_1(A_18)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_586,plain,(
    ! [A_79,B_80] :
      ( k4_subset_1(A_79,B_80,k3_subset_1(A_79,B_80)) = A_79
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_594,plain,(
    ! [B_23,A_22] :
      ( k4_subset_1(B_23,A_22,k3_subset_1(B_23,A_22)) = B_23
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_586])).

tff(c_1210,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski(k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1196,c_594])).

tff(c_1231,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_562,c_557,c_562,c_1210])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_116,plain,(
    ! [A_50,B_51] : k2_xboole_0(A_50,k2_xboole_0(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_1505,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_134])).

tff(c_1519,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1505])).

tff(c_148,plain,(
    ! [B_54,A_55] : k2_xboole_0(B_54,k2_xboole_0(A_55,B_54)) = k2_xboole_0(B_54,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_164,plain,(
    ! [A_1,B_2] : k2_xboole_0(k2_xboole_0(A_1,B_2),k2_xboole_0(B_2,A_1)) = k2_xboole_0(k2_xboole_0(A_1,B_2),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_148])).

tff(c_228,plain,(
    ! [A_64,B_65] : k2_xboole_0(k2_xboole_0(A_64,B_65),k2_xboole_0(B_65,A_64)) = k2_xboole_0(B_65,A_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_2,c_164])).

tff(c_285,plain,(
    ! [A_1,B_2] : k2_xboole_0(k2_xboole_0(A_1,B_2),k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_228])).

tff(c_1813,plain,(
    k2_xboole_0(k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')),k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1519,c_285])).

tff(c_1855,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1231,c_6,c_2,c_1231,c_2,c_1813])).

tff(c_1166,plain,(
    ! [A_119,B_120] :
      ( k4_subset_1(u1_struct_0(A_119),B_120,k2_tops_1(A_119,B_120)) = k2_pre_topc(A_119,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1176,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1166])).

tff(c_1182,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1176])).

tff(c_883,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(k2_tops_1(A_92,B_93),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_907,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k2_tops_1(A_92,B_93),u1_struct_0(A_92))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_883,c_22])).

tff(c_1124,plain,(
    ! [A_115] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_115) = k2_xboole_0('#skF_2',A_115)
      | ~ r1_tarski(A_115,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1105])).

tff(c_1128,plain,(
    ! [B_93] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_93)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_907,c_1124])).

tff(c_1930,plain,(
    ! [B_140] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_140)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_140))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1128])).

tff(c_1945,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_1930])).

tff(c_1952,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1855,c_1182,c_1945])).

tff(c_1954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1029,c_1952])).

tff(c_1955,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2237,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2236,c_1955])).

tff(c_2276,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2275,c_2237])).

tff(c_1956,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2607,plain,(
    ! [A_179,B_180] :
      ( k2_pre_topc(A_179,B_180) = B_180
      | ~ v4_pre_topc(B_180,A_179)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2618,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2607])).

tff(c_2623,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1956,c_2618])).

tff(c_3092,plain,(
    ! [A_215,B_216] :
      ( k7_subset_1(u1_struct_0(A_215),k2_pre_topc(A_215,B_216),k1_tops_1(A_215,B_216)) = k2_tops_1(A_215,B_216)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3101,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2623,c_3092])).

tff(c_3105,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2275,c_2236,c_3101])).

tff(c_3107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2276,c_3105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/1.85  
% 4.75/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/1.85  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 4.75/1.85  
% 4.75/1.85  %Foreground sorts:
% 4.75/1.85  
% 4.75/1.85  
% 4.75/1.85  %Background operators:
% 4.75/1.85  
% 4.75/1.85  
% 4.75/1.85  %Foreground operators:
% 4.75/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.75/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.75/1.85  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.75/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.75/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.75/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.75/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.75/1.85  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.75/1.85  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.75/1.85  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.75/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.75/1.85  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.75/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.75/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.75/1.85  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.75/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.75/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.75/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.75/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.75/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.75/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.75/1.85  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.75/1.85  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.75/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.75/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.75/1.85  
% 4.75/1.87  tff(f_123, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.75/1.87  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.75/1.87  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.75/1.87  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.75/1.87  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.75/1.87  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.75/1.87  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.75/1.87  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.75/1.87  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.75/1.87  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 4.75/1.87  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 4.75/1.87  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.75/1.87  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.75/1.87  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.75/1.87  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.75/1.87  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.75/1.87  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.75/1.87  tff(c_2255, plain, (![A_166, B_167]: (r1_tarski(k1_tops_1(A_166, B_167), B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.75/1.87  tff(c_2263, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2255])).
% 4.75/1.87  tff(c_2268, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2263])).
% 4.75/1.87  tff(c_24, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.75/1.87  tff(c_2031, plain, (![A_147, B_148]: (k4_xboole_0(A_147, B_148)=k3_subset_1(A_147, B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.75/1.87  tff(c_2038, plain, (![B_23, A_22]: (k4_xboole_0(B_23, A_22)=k3_subset_1(B_23, A_22) | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_24, c_2031])).
% 4.75/1.87  tff(c_2275, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2268, c_2038])).
% 4.75/1.87  tff(c_2227, plain, (![A_159, B_160, C_161]: (k7_subset_1(A_159, B_160, C_161)=k4_xboole_0(B_160, C_161) | ~m1_subset_1(B_160, k1_zfmisc_1(A_159)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.75/1.87  tff(c_2236, plain, (![C_161]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_161)=k4_xboole_0('#skF_2', C_161))), inference(resolution, [status(thm)], [c_40, c_2227])).
% 4.75/1.87  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.75/1.87  tff(c_115, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.75/1.87  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.75/1.87  tff(c_1008, plain, (![B_105, A_106]: (v4_pre_topc(B_105, A_106) | k2_pre_topc(A_106, B_105)!=B_105 | ~v2_pre_topc(A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.75/1.87  tff(c_1022, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1008])).
% 4.75/1.87  tff(c_1028, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1022])).
% 4.75/1.87  tff(c_1029, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_115, c_1028])).
% 4.75/1.87  tff(c_544, plain, (![A_74, B_75]: (r1_tarski(k1_tops_1(A_74, B_75), B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.75/1.87  tff(c_552, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_544])).
% 4.75/1.87  tff(c_557, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_552])).
% 4.75/1.87  tff(c_514, plain, (![A_70, B_71, C_72]: (k7_subset_1(A_70, B_71, C_72)=k4_xboole_0(B_71, C_72) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.75/1.87  tff(c_524, plain, (![C_73]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_73)=k4_xboole_0('#skF_2', C_73))), inference(resolution, [status(thm)], [c_40, c_514])).
% 4.75/1.87  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.75/1.87  tff(c_213, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_115, c_52])).
% 4.75/1.87  tff(c_530, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_524, c_213])).
% 4.75/1.87  tff(c_196, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.75/1.87  tff(c_207, plain, (![B_23, A_22]: (k4_xboole_0(B_23, A_22)=k3_subset_1(B_23, A_22) | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_24, c_196])).
% 4.75/1.87  tff(c_560, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_557, c_207])).
% 4.75/1.87  tff(c_562, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_530, c_560])).
% 4.75/1.87  tff(c_190, plain, (![A_56, B_57]: (m1_subset_1(k3_subset_1(A_56, B_57), k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.75/1.87  tff(c_22, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.75/1.87  tff(c_194, plain, (![A_56, B_57]: (r1_tarski(k3_subset_1(A_56, B_57), A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(resolution, [status(thm)], [c_190, c_22])).
% 4.75/1.87  tff(c_566, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_562, c_194])).
% 4.75/1.87  tff(c_660, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_566])).
% 4.75/1.87  tff(c_663, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_660])).
% 4.75/1.87  tff(c_667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_557, c_663])).
% 4.75/1.87  tff(c_668, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_566])).
% 4.75/1.87  tff(c_669, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_566])).
% 4.75/1.87  tff(c_934, plain, (![A_95, B_96, C_97]: (k4_subset_1(A_95, B_96, C_97)=k2_xboole_0(B_96, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(A_95)) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.75/1.87  tff(c_1105, plain, (![B_112, B_113, A_114]: (k4_subset_1(B_112, B_113, A_114)=k2_xboole_0(B_113, A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(B_112)) | ~r1_tarski(A_114, B_112))), inference(resolution, [status(thm)], [c_24, c_934])).
% 4.75/1.87  tff(c_1196, plain, (![A_122]: (k4_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'), A_122)=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), A_122) | ~r1_tarski(A_122, '#skF_2'))), inference(resolution, [status(thm)], [c_669, c_1105])).
% 4.75/1.87  tff(c_8, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.75/1.87  tff(c_18, plain, (![A_18, B_19]: (k4_subset_1(A_18, B_19, k3_subset_1(A_18, B_19))=k2_subset_1(A_18) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.75/1.87  tff(c_586, plain, (![A_79, B_80]: (k4_subset_1(A_79, B_80, k3_subset_1(A_79, B_80))=A_79 | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 4.75/1.87  tff(c_594, plain, (![B_23, A_22]: (k4_subset_1(B_23, A_22, k3_subset_1(B_23, A_22))=B_23 | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_24, c_586])).
% 4.75/1.87  tff(c_1210, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2')))='#skF_2' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2')), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1196, c_594])).
% 4.75/1.87  tff(c_1231, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_668, c_562, c_557, c_562, c_1210])).
% 4.75/1.87  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.75/1.87  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.75/1.87  tff(c_116, plain, (![A_50, B_51]: (k2_xboole_0(A_50, k2_xboole_0(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.75/1.87  tff(c_134, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_116])).
% 4.75/1.87  tff(c_1505, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1231, c_134])).
% 4.75/1.87  tff(c_1519, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1505])).
% 4.75/1.87  tff(c_148, plain, (![B_54, A_55]: (k2_xboole_0(B_54, k2_xboole_0(A_55, B_54))=k2_xboole_0(B_54, A_55))), inference(superposition, [status(thm), theory('equality')], [c_2, c_116])).
% 4.75/1.87  tff(c_164, plain, (![A_1, B_2]: (k2_xboole_0(k2_xboole_0(A_1, B_2), k2_xboole_0(B_2, A_1))=k2_xboole_0(k2_xboole_0(A_1, B_2), B_2))), inference(superposition, [status(thm), theory('equality')], [c_134, c_148])).
% 4.75/1.87  tff(c_228, plain, (![A_64, B_65]: (k2_xboole_0(k2_xboole_0(A_64, B_65), k2_xboole_0(B_65, A_64))=k2_xboole_0(B_65, A_64))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_2, c_164])).
% 4.75/1.87  tff(c_285, plain, (![A_1, B_2]: (k2_xboole_0(k2_xboole_0(A_1, B_2), k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_228])).
% 4.75/1.87  tff(c_1813, plain, (k2_xboole_0(k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')), k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2')))=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1519, c_285])).
% 4.75/1.87  tff(c_1855, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1231, c_6, c_2, c_1231, c_2, c_1813])).
% 4.75/1.87  tff(c_1166, plain, (![A_119, B_120]: (k4_subset_1(u1_struct_0(A_119), B_120, k2_tops_1(A_119, B_120))=k2_pre_topc(A_119, B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.75/1.87  tff(c_1176, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1166])).
% 4.75/1.87  tff(c_1182, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1176])).
% 4.75/1.87  tff(c_883, plain, (![A_92, B_93]: (m1_subset_1(k2_tops_1(A_92, B_93), k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.75/1.87  tff(c_907, plain, (![A_92, B_93]: (r1_tarski(k2_tops_1(A_92, B_93), u1_struct_0(A_92)) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_883, c_22])).
% 4.75/1.87  tff(c_1124, plain, (![A_115]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_115)=k2_xboole_0('#skF_2', A_115) | ~r1_tarski(A_115, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_1105])).
% 4.75/1.87  tff(c_1128, plain, (![B_93]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_93))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_93)) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_907, c_1124])).
% 4.75/1.87  tff(c_1930, plain, (![B_140]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_140))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_140)) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1128])).
% 4.75/1.87  tff(c_1945, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1930])).
% 4.75/1.87  tff(c_1952, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1855, c_1182, c_1945])).
% 4.75/1.87  tff(c_1954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1029, c_1952])).
% 4.75/1.87  tff(c_1955, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 4.75/1.87  tff(c_2237, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2236, c_1955])).
% 4.75/1.87  tff(c_2276, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2275, c_2237])).
% 4.75/1.87  tff(c_1956, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.75/1.87  tff(c_2607, plain, (![A_179, B_180]: (k2_pre_topc(A_179, B_180)=B_180 | ~v4_pre_topc(B_180, A_179) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.75/1.87  tff(c_2618, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2607])).
% 4.75/1.87  tff(c_2623, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1956, c_2618])).
% 4.75/1.87  tff(c_3092, plain, (![A_215, B_216]: (k7_subset_1(u1_struct_0(A_215), k2_pre_topc(A_215, B_216), k1_tops_1(A_215, B_216))=k2_tops_1(A_215, B_216) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.75/1.87  tff(c_3101, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2623, c_3092])).
% 4.75/1.87  tff(c_3105, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2275, c_2236, c_3101])).
% 4.75/1.87  tff(c_3107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2276, c_3105])).
% 4.75/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/1.87  
% 4.75/1.87  Inference rules
% 4.75/1.87  ----------------------
% 4.75/1.87  #Ref     : 0
% 4.75/1.87  #Sup     : 744
% 4.75/1.87  #Fact    : 0
% 4.75/1.87  #Define  : 0
% 4.75/1.87  #Split   : 2
% 4.75/1.87  #Chain   : 0
% 4.75/1.87  #Close   : 0
% 4.75/1.87  
% 4.75/1.87  Ordering : KBO
% 4.75/1.87  
% 4.75/1.87  Simplification rules
% 4.75/1.87  ----------------------
% 4.75/1.87  #Subsume      : 68
% 4.75/1.87  #Demod        : 898
% 4.75/1.87  #Tautology    : 467
% 4.75/1.87  #SimpNegUnit  : 6
% 4.75/1.87  #BackRed      : 6
% 4.75/1.87  
% 4.75/1.87  #Partial instantiations: 0
% 4.75/1.87  #Strategies tried      : 1
% 4.75/1.87  
% 4.75/1.87  Timing (in seconds)
% 4.75/1.87  ----------------------
% 4.75/1.87  Preprocessing        : 0.36
% 4.75/1.88  Parsing              : 0.20
% 4.75/1.88  CNF conversion       : 0.02
% 4.75/1.88  Main loop            : 0.71
% 4.75/1.88  Inferencing          : 0.21
% 4.75/1.88  Reduction            : 0.33
% 4.75/1.88  Demodulation         : 0.27
% 4.75/1.88  BG Simplification    : 0.03
% 4.75/1.88  Subsumption          : 0.09
% 4.75/1.88  Abstraction          : 0.04
% 4.75/1.88  MUC search           : 0.00
% 4.75/1.88  Cooper               : 0.00
% 4.75/1.88  Total                : 1.12
% 4.75/1.88  Index Insertion      : 0.00
% 4.75/1.88  Index Deletion       : 0.00
% 4.75/1.88  Index Matching       : 0.00
% 4.75/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
