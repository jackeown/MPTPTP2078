%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:31 EST 2020

% Result     : Theorem 23.21s
% Output     : CNFRefutation 23.53s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 820 expanded)
%              Number of leaves         :   37 ( 291 expanded)
%              Depth                    :   23
%              Number of atoms          :  211 (1159 expanded)
%              Number of equality atoms :  112 ( 592 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_82,axiom,(
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

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_100705,plain,(
    ! [A_812,B_813,C_814] :
      ( k7_subset_1(A_812,B_813,C_814) = k4_xboole_0(B_813,C_814)
      | ~ m1_subset_1(B_813,k1_zfmisc_1(A_812)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_100711,plain,(
    ! [C_814] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_814) = k4_xboole_0('#skF_2',C_814) ),
    inference(resolution,[status(thm)],[c_44,c_100705])).

tff(c_56,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_120,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_204,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2137,plain,(
    ! [B_136,A_137] :
      ( v4_pre_topc(B_136,A_137)
      | k2_pre_topc(A_137,B_136) != B_136
      | ~ v2_pre_topc(A_137)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2147,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2137])).

tff(c_2152,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_2147])).

tff(c_2153,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_2152])).

tff(c_2310,plain,(
    ! [A_143,B_144] :
      ( k4_subset_1(u1_struct_0(A_143),B_144,k2_tops_1(A_143,B_144)) = k2_pre_topc(A_143,B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2317,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2310])).

tff(c_2322,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2317])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_tops_1(A_31,B_32),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1836,plain,(
    ! [A_125,B_126,C_127] :
      ( k4_subset_1(A_125,B_126,C_127) = k2_xboole_0(B_126,C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26125,plain,(
    ! [A_397,B_398,B_399] :
      ( k4_subset_1(u1_struct_0(A_397),B_398,k2_tops_1(A_397,B_399)) = k2_xboole_0(B_398,k2_tops_1(A_397,B_399))
      | ~ m1_subset_1(B_398,k1_zfmisc_1(u1_struct_0(A_397)))
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0(A_397)))
      | ~ l1_pre_topc(A_397) ) ),
    inference(resolution,[status(thm)],[c_36,c_1836])).

tff(c_26132,plain,(
    ! [B_399] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_399)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_399))
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_26125])).

tff(c_26350,plain,(
    ! [B_400] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_400)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_400))
      | ~ m1_subset_1(B_400,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_26132])).

tff(c_26361,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_26350])).

tff(c_26367,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2322,c_26361])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_223,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_134,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(A_53,B_54) = B_54
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_171,plain,(
    ! [A_58,B_59] : k2_xboole_0(k4_xboole_0(A_58,B_59),A_58) = A_58 ),
    inference(resolution,[status(thm)],[c_16,c_134])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_178,plain,(
    ! [B_59] : k4_xboole_0(k1_xboole_0,B_59) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_12])).

tff(c_256,plain,(
    ! [B_65] : k3_xboole_0(k1_xboole_0,B_65) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_178])).

tff(c_282,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_256])).

tff(c_339,plain,(
    ! [A_67,B_68] : r1_tarski(k3_xboole_0(A_67,B_68),A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_16])).

tff(c_350,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_339])).

tff(c_415,plain,(
    ! [A_72] : r1_tarski(k1_xboole_0,A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_339])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_425,plain,(
    ! [A_72] : k2_xboole_0(k1_xboole_0,A_72) = A_72 ),
    inference(resolution,[status(thm)],[c_415,c_10])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_493,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_tarski(A_76,k2_xboole_0(B_77,C_78))
      | ~ r1_tarski(k4_xboole_0(A_76,B_77),C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_772,plain,(
    ! [A_92,B_93] : r1_tarski(A_92,k2_xboole_0(B_93,k4_xboole_0(A_92,B_93))) ),
    inference(resolution,[status(thm)],[c_8,c_493])).

tff(c_804,plain,(
    ! [A_94] : r1_tarski(A_94,k4_xboole_0(A_94,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_772])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_810,plain,(
    ! [A_94] :
      ( k4_xboole_0(A_94,k1_xboole_0) = A_94
      | ~ r1_tarski(k4_xboole_0(A_94,k1_xboole_0),A_94) ) ),
    inference(resolution,[status(thm)],[c_804,c_4])).

tff(c_836,plain,(
    ! [A_95] : k4_xboole_0(A_95,k1_xboole_0) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_810])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_855,plain,(
    ! [A_95] : k4_xboole_0(A_95,A_95) = k3_xboole_0(A_95,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_22])).

tff(c_889,plain,(
    ! [A_96] : k4_xboole_0(A_96,A_96) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_855])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_tarski(A_15,k2_xboole_0(B_16,C_17))
      | ~ r1_tarski(k4_xboole_0(A_15,B_16),C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_901,plain,(
    ! [A_96,C_17] :
      ( r1_tarski(A_96,k2_xboole_0(A_96,C_17))
      | ~ r1_tarski(k1_xboole_0,C_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_20])).

tff(c_957,plain,(
    ! [A_99,C_100] : r1_tarski(A_99,k2_xboole_0(A_99,C_100)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_901])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_994,plain,(
    ! [A_99,C_100] : k3_xboole_0(A_99,k2_xboole_0(A_99,C_100)) = A_99 ),
    inference(resolution,[status(thm)],[c_957,c_14])).

tff(c_26445,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_26367,c_994])).

tff(c_683,plain,(
    ! [A_86,B_87,C_88] :
      ( k7_subset_1(A_86,B_87,C_88) = k4_xboole_0(B_87,C_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_756,plain,(
    ! [C_91] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_91) = k4_xboole_0('#skF_2',C_91) ),
    inference(resolution,[status(thm)],[c_44,c_683])).

tff(c_768,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_756])).

tff(c_145,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_16,c_134])).

tff(c_514,plain,(
    ! [A_79,B_80] : r1_tarski(A_79,k2_xboole_0(B_80,A_79)) ),
    inference(resolution,[status(thm)],[c_16,c_493])).

tff(c_544,plain,(
    ! [A_79,B_80] : k2_xboole_0(A_79,k2_xboole_0(B_80,A_79)) = k2_xboole_0(B_80,A_79) ),
    inference(resolution,[status(thm)],[c_514,c_10])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k4_xboole_0(A_12,B_13),C_14) = k4_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_372,plain,(
    ! [A_69,B_70,C_71] : k4_xboole_0(k4_xboole_0(A_69,B_70),C_71) = k4_xboole_0(A_69,k2_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_375,plain,(
    ! [A_69,B_70,C_71,C_14] : k4_xboole_0(k4_xboole_0(A_69,k2_xboole_0(B_70,C_71)),C_14) = k4_xboole_0(k4_xboole_0(A_69,B_70),k2_xboole_0(C_71,C_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_18])).

tff(c_408,plain,(
    ! [A_69,B_70,C_71,C_14] : k4_xboole_0(A_69,k2_xboole_0(k2_xboole_0(B_70,C_71),C_14)) = k4_xboole_0(A_69,k2_xboole_0(B_70,k2_xboole_0(C_71,C_14))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_375])).

tff(c_904,plain,(
    ! [A_96,C_14] : k4_xboole_0(A_96,k2_xboole_0(A_96,C_14)) = k4_xboole_0(k1_xboole_0,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_18])).

tff(c_1053,plain,(
    ! [A_101,C_102] : k4_xboole_0(A_101,k2_xboole_0(A_101,C_102)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_904])).

tff(c_1240,plain,(
    ! [A_107,B_108] : k4_xboole_0(k4_xboole_0(A_107,B_108),A_107) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_1053])).

tff(c_1301,plain,(
    ! [C_14,B_13] : k4_xboole_0(C_14,k2_xboole_0(B_13,C_14)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1240])).

tff(c_882,plain,(
    ! [A_95] : k4_xboole_0(A_95,A_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_855])).

tff(c_146,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_11305,plain,(
    ! [A_277,B_278,C_279] : k4_xboole_0(k4_xboole_0(A_277,B_278),k4_xboole_0(A_277,k2_xboole_0(B_278,C_279))) = k3_xboole_0(k4_xboole_0(A_277,B_278),C_279) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_22])).

tff(c_11534,plain,(
    ! [A_277,B_4] : k4_xboole_0(k4_xboole_0(A_277,B_4),k4_xboole_0(A_277,B_4)) = k3_xboole_0(k4_xboole_0(A_277,B_4),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_11305])).

tff(c_11605,plain,(
    ! [B_280,A_281] : k3_xboole_0(B_280,k4_xboole_0(A_281,B_280)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_882,c_2,c_11534])).

tff(c_102,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3268,plain,(
    ! [A_179,B_180] : k3_xboole_0(k4_xboole_0(A_179,B_180),A_179) = k4_xboole_0(A_179,B_180) ),
    inference(resolution,[status(thm)],[c_16,c_102])).

tff(c_3399,plain,(
    ! [A_1,B_180] : k3_xboole_0(A_1,k4_xboole_0(A_1,B_180)) = k4_xboole_0(A_1,B_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3268])).

tff(c_226,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,k4_xboole_0(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_22])).

tff(c_5110,plain,(
    ! [A_217,B_218] : k4_xboole_0(A_217,k3_xboole_0(A_217,B_218)) = k4_xboole_0(A_217,B_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3399,c_226])).

tff(c_5229,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5110])).

tff(c_11628,plain,(
    ! [A_281,B_280] : k4_xboole_0(k4_xboole_0(A_281,B_280),k1_xboole_0) = k4_xboole_0(k4_xboole_0(A_281,B_280),B_280) ),
    inference(superposition,[status(thm),theory(equality)],[c_11605,c_5229])).

tff(c_17668,plain,(
    ! [A_329,B_330] : k4_xboole_0(k4_xboole_0(A_329,B_330),B_330) = k4_xboole_0(A_329,B_330) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18,c_11628])).

tff(c_404,plain,(
    ! [A_69,B_70,B_19] : k4_xboole_0(A_69,k2_xboole_0(B_70,k4_xboole_0(k4_xboole_0(A_69,B_70),B_19))) = k3_xboole_0(k4_xboole_0(A_69,B_70),B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_372])).

tff(c_413,plain,(
    ! [A_69,B_70,B_19] : k4_xboole_0(A_69,k2_xboole_0(B_70,k4_xboole_0(A_69,k2_xboole_0(B_70,B_19)))) = k3_xboole_0(k4_xboole_0(A_69,B_70),B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_404])).

tff(c_17694,plain,(
    ! [A_329,B_70,B_19] : k4_xboole_0(k4_xboole_0(A_329,k2_xboole_0(B_70,B_19)),k2_xboole_0(B_70,k4_xboole_0(A_329,k2_xboole_0(B_70,B_19)))) = k3_xboole_0(k4_xboole_0(k4_xboole_0(A_329,k2_xboole_0(B_70,B_19)),B_70),B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_17668,c_413])).

tff(c_40041,plain,(
    ! [B_498,A_499,B_500] : k3_xboole_0(B_498,k4_xboole_0(A_499,k2_xboole_0(B_498,B_500))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_408,c_1301,c_18,c_2,c_17694])).

tff(c_60863,plain,(
    ! [A_605,B_606,A_607] : k3_xboole_0(k4_xboole_0(A_605,B_606),k4_xboole_0(A_607,A_605)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_40041])).

tff(c_61482,plain,(
    ! [A_607] : k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),k4_xboole_0(A_607,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_60863])).

tff(c_43271,plain,(
    ! [A_518,B_519,C_520] : r1_tarski(k4_xboole_0(A_518,B_519),k2_xboole_0(C_520,k4_xboole_0(A_518,k2_xboole_0(B_519,C_520)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_772])).

tff(c_43604,plain,(
    ! [B_519,C_520] : r1_tarski(k4_xboole_0(k2_xboole_0(B_519,C_520),B_519),k2_xboole_0(C_520,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_43271])).

tff(c_43740,plain,(
    ! [B_521,C_522] : r1_tarski(k4_xboole_0(k2_xboole_0(B_521,C_522),B_521),C_522) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_43604])).

tff(c_43908,plain,(
    ! [B_523,C_524] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_523,C_524),B_523),C_524) = C_524 ),
    inference(resolution,[status(thm)],[c_43740,c_10])).

tff(c_939,plain,(
    ! [A_96,C_14] : k4_xboole_0(A_96,k2_xboole_0(A_96,C_14)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_904])).

tff(c_44530,plain,(
    ! [B_527,C_528] : k4_xboole_0(k4_xboole_0(k2_xboole_0(B_527,C_528),B_527),C_528) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_43908,c_939])).

tff(c_44748,plain,(
    k4_xboole_0(k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26367,c_44530])).

tff(c_630,plain,(
    ! [A_84,B_85] : k2_xboole_0(k3_xboole_0(A_84,B_85),A_84) = A_84 ),
    inference(resolution,[status(thm)],[c_339,c_10])).

tff(c_667,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_630])).

tff(c_1088,plain,(
    ! [A_1,B_2] : k4_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_1053])).

tff(c_5625,plain,(
    ! [A_223,B_224,C_225] : k4_xboole_0(A_223,k2_xboole_0(k4_xboole_0(A_223,B_224),C_225)) = k4_xboole_0(k3_xboole_0(A_223,B_224),C_225) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_372])).

tff(c_513,plain,(
    ! [A_76,B_77] : r1_tarski(A_76,k2_xboole_0(B_77,k4_xboole_0(A_76,B_77))) ),
    inference(resolution,[status(thm)],[c_8,c_493])).

tff(c_71842,plain,(
    ! [A_666,B_667,C_668] : r1_tarski(A_666,k2_xboole_0(k2_xboole_0(k4_xboole_0(A_666,B_667),C_668),k4_xboole_0(k3_xboole_0(A_666,B_667),C_668))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5625,c_513])).

tff(c_72345,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(k2_xboole_0(k4_xboole_0(A_1,B_2),B_2),k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_71842])).

tff(c_72587,plain,(
    ! [A_669,B_670] : r1_tarski(A_669,k2_xboole_0(k4_xboole_0(A_669,B_670),B_670)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_72345])).

tff(c_72855,plain,(
    ! [A_669,B_670] : k3_xboole_0(A_669,k2_xboole_0(k4_xboole_0(A_669,B_670),B_670)) = A_669 ),
    inference(resolution,[status(thm)],[c_72587,c_14])).

tff(c_99361,plain,(
    k3_xboole_0(k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2'),k2_xboole_0(k1_xboole_0,k2_tops_1('#skF_1','#skF_2'))) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_44748,c_72855])).

tff(c_99564,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61482,c_2,c_425,c_99361])).

tff(c_110,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_102])).

tff(c_72921,plain,(
    ! [A_671,B_672] : k3_xboole_0(A_671,k2_xboole_0(k4_xboole_0(A_671,B_672),B_672)) = A_671 ),
    inference(resolution,[status(thm)],[c_72587,c_14])).

tff(c_457,plain,(
    ! [A_74,B_75] : r1_tarski(k3_xboole_0(A_74,B_75),B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_339])).

tff(c_7913,plain,(
    ! [A_250,B_251] : k3_xboole_0(k3_xboole_0(A_250,B_251),B_251) = k3_xboole_0(A_250,B_251) ),
    inference(resolution,[status(thm)],[c_457,c_14])).

tff(c_8975,plain,(
    ! [B_258,A_259] : k3_xboole_0(k3_xboole_0(B_258,A_259),B_258) = k3_xboole_0(A_259,B_258) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7913])).

tff(c_9208,plain,(
    ! [A_1,A_259] : k3_xboole_0(A_1,k3_xboole_0(A_1,A_259)) = k3_xboole_0(A_259,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8975])).

tff(c_73150,plain,(
    ! [A_671,B_672] : k3_xboole_0(k2_xboole_0(k4_xboole_0(A_671,B_672),B_672),A_671) = k3_xboole_0(A_671,A_671) ),
    inference(superposition,[status(thm),theory(equality)],[c_72921,c_9208])).

tff(c_73624,plain,(
    ! [A_671,B_672] : k3_xboole_0(k2_xboole_0(k4_xboole_0(A_671,B_672),B_672),A_671) = A_671 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_73150])).

tff(c_99653,plain,(
    k3_xboole_0(k2_xboole_0(k1_xboole_0,'#skF_2'),k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_99564,c_73624])).

tff(c_99887,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26445,c_425,c_99653])).

tff(c_99889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2153,c_99887])).

tff(c_99890,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_100145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_99890])).

tff(c_100146,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_100231,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100146,c_50])).

tff(c_100778,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100711,c_100231])).

tff(c_101613,plain,(
    ! [A_845,B_846] :
      ( k2_pre_topc(A_845,B_846) = B_846
      | ~ v4_pre_topc(B_846,A_845)
      | ~ m1_subset_1(B_846,k1_zfmisc_1(u1_struct_0(A_845)))
      | ~ l1_pre_topc(A_845) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_101623,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_101613])).

tff(c_101628,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_100146,c_101623])).

tff(c_103152,plain,(
    ! [A_904,B_905] :
      ( k7_subset_1(u1_struct_0(A_904),k2_pre_topc(A_904,B_905),k1_tops_1(A_904,B_905)) = k2_tops_1(A_904,B_905)
      | ~ m1_subset_1(B_905,k1_zfmisc_1(u1_struct_0(A_904)))
      | ~ l1_pre_topc(A_904) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_103161,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_101628,c_103152])).

tff(c_103165,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_100711,c_103161])).

tff(c_103167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100778,c_103165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.21/15.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.21/15.66  
% 23.21/15.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.21/15.66  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 23.21/15.66  
% 23.21/15.66  %Foreground sorts:
% 23.21/15.66  
% 23.21/15.66  
% 23.21/15.66  %Background operators:
% 23.21/15.66  
% 23.21/15.66  
% 23.21/15.66  %Foreground operators:
% 23.21/15.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.21/15.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.21/15.66  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 23.21/15.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.21/15.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 23.21/15.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.21/15.66  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 23.21/15.66  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 23.21/15.66  tff('#skF_2', type, '#skF_2': $i).
% 23.21/15.66  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 23.21/15.66  tff('#skF_1', type, '#skF_1': $i).
% 23.21/15.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.21/15.66  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 23.21/15.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.21/15.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.21/15.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 23.21/15.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.21/15.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.21/15.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.21/15.66  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 23.21/15.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.21/15.66  
% 23.53/15.69  tff(f_122, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 23.53/15.69  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 23.53/15.69  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 23.53/15.69  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 23.53/15.69  tff(f_88, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 23.53/15.69  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 23.53/15.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 23.53/15.69  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 23.53/15.69  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 23.53/15.69  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 23.53/15.69  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 23.53/15.69  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.53/15.69  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 23.53/15.69  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 23.53/15.69  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 23.53/15.69  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 23.53/15.69  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 23.53/15.69  tff(c_100705, plain, (![A_812, B_813, C_814]: (k7_subset_1(A_812, B_813, C_814)=k4_xboole_0(B_813, C_814) | ~m1_subset_1(B_813, k1_zfmisc_1(A_812)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.53/15.69  tff(c_100711, plain, (![C_814]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_814)=k4_xboole_0('#skF_2', C_814))), inference(resolution, [status(thm)], [c_44, c_100705])).
% 23.53/15.69  tff(c_56, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 23.53/15.69  tff(c_120, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 23.53/15.69  tff(c_50, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 23.53/15.69  tff(c_204, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 23.53/15.69  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 23.53/15.69  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 23.53/15.69  tff(c_2137, plain, (![B_136, A_137]: (v4_pre_topc(B_136, A_137) | k2_pre_topc(A_137, B_136)!=B_136 | ~v2_pre_topc(A_137) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_82])).
% 23.53/15.69  tff(c_2147, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2137])).
% 23.53/15.69  tff(c_2152, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_2147])).
% 23.53/15.69  tff(c_2153, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_204, c_2152])).
% 23.53/15.69  tff(c_2310, plain, (![A_143, B_144]: (k4_subset_1(u1_struct_0(A_143), B_144, k2_tops_1(A_143, B_144))=k2_pre_topc(A_143, B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_110])).
% 23.53/15.69  tff(c_2317, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2310])).
% 23.53/15.69  tff(c_2322, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2317])).
% 23.53/15.69  tff(c_36, plain, (![A_31, B_32]: (m1_subset_1(k2_tops_1(A_31, B_32), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_88])).
% 23.53/15.69  tff(c_1836, plain, (![A_125, B_126, C_127]: (k4_subset_1(A_125, B_126, C_127)=k2_xboole_0(B_126, C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(A_125)) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.53/15.69  tff(c_26125, plain, (![A_397, B_398, B_399]: (k4_subset_1(u1_struct_0(A_397), B_398, k2_tops_1(A_397, B_399))=k2_xboole_0(B_398, k2_tops_1(A_397, B_399)) | ~m1_subset_1(B_398, k1_zfmisc_1(u1_struct_0(A_397))) | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0(A_397))) | ~l1_pre_topc(A_397))), inference(resolution, [status(thm)], [c_36, c_1836])).
% 23.53/15.69  tff(c_26132, plain, (![B_399]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_399))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_399)) | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_26125])).
% 23.53/15.69  tff(c_26350, plain, (![B_400]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_400))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_400)) | ~m1_subset_1(B_400, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_26132])).
% 23.53/15.69  tff(c_26361, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_26350])).
% 23.53/15.69  tff(c_26367, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2322, c_26361])).
% 23.53/15.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.53/15.69  tff(c_223, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.53/15.69  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.53/15.69  tff(c_134, plain, (![A_53, B_54]: (k2_xboole_0(A_53, B_54)=B_54 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.53/15.69  tff(c_171, plain, (![A_58, B_59]: (k2_xboole_0(k4_xboole_0(A_58, B_59), A_58)=A_58)), inference(resolution, [status(thm)], [c_16, c_134])).
% 23.53/15.69  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 23.53/15.69  tff(c_178, plain, (![B_59]: (k4_xboole_0(k1_xboole_0, B_59)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_171, c_12])).
% 23.53/15.69  tff(c_256, plain, (![B_65]: (k3_xboole_0(k1_xboole_0, B_65)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_223, c_178])).
% 23.53/15.69  tff(c_282, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_256])).
% 23.53/15.69  tff(c_339, plain, (![A_67, B_68]: (r1_tarski(k3_xboole_0(A_67, B_68), A_67))), inference(superposition, [status(thm), theory('equality')], [c_223, c_16])).
% 23.53/15.69  tff(c_350, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(superposition, [status(thm), theory('equality')], [c_282, c_339])).
% 23.53/15.69  tff(c_415, plain, (![A_72]: (r1_tarski(k1_xboole_0, A_72))), inference(superposition, [status(thm), theory('equality')], [c_282, c_339])).
% 23.53/15.69  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.53/15.69  tff(c_425, plain, (![A_72]: (k2_xboole_0(k1_xboole_0, A_72)=A_72)), inference(resolution, [status(thm)], [c_415, c_10])).
% 23.53/15.69  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.53/15.69  tff(c_493, plain, (![A_76, B_77, C_78]: (r1_tarski(A_76, k2_xboole_0(B_77, C_78)) | ~r1_tarski(k4_xboole_0(A_76, B_77), C_78))), inference(cnfTransformation, [status(thm)], [f_51])).
% 23.53/15.69  tff(c_772, plain, (![A_92, B_93]: (r1_tarski(A_92, k2_xboole_0(B_93, k4_xboole_0(A_92, B_93))))), inference(resolution, [status(thm)], [c_8, c_493])).
% 23.53/15.69  tff(c_804, plain, (![A_94]: (r1_tarski(A_94, k4_xboole_0(A_94, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_425, c_772])).
% 23.53/15.69  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.53/15.69  tff(c_810, plain, (![A_94]: (k4_xboole_0(A_94, k1_xboole_0)=A_94 | ~r1_tarski(k4_xboole_0(A_94, k1_xboole_0), A_94))), inference(resolution, [status(thm)], [c_804, c_4])).
% 23.53/15.69  tff(c_836, plain, (![A_95]: (k4_xboole_0(A_95, k1_xboole_0)=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_810])).
% 23.53/15.69  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.53/15.69  tff(c_855, plain, (![A_95]: (k4_xboole_0(A_95, A_95)=k3_xboole_0(A_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_836, c_22])).
% 23.53/15.69  tff(c_889, plain, (![A_96]: (k4_xboole_0(A_96, A_96)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_282, c_855])).
% 23.53/15.69  tff(c_20, plain, (![A_15, B_16, C_17]: (r1_tarski(A_15, k2_xboole_0(B_16, C_17)) | ~r1_tarski(k4_xboole_0(A_15, B_16), C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 23.53/15.69  tff(c_901, plain, (![A_96, C_17]: (r1_tarski(A_96, k2_xboole_0(A_96, C_17)) | ~r1_tarski(k1_xboole_0, C_17))), inference(superposition, [status(thm), theory('equality')], [c_889, c_20])).
% 23.53/15.69  tff(c_957, plain, (![A_99, C_100]: (r1_tarski(A_99, k2_xboole_0(A_99, C_100)))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_901])).
% 23.53/15.69  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.53/15.69  tff(c_994, plain, (![A_99, C_100]: (k3_xboole_0(A_99, k2_xboole_0(A_99, C_100))=A_99)), inference(resolution, [status(thm)], [c_957, c_14])).
% 23.53/15.69  tff(c_26445, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_26367, c_994])).
% 23.53/15.69  tff(c_683, plain, (![A_86, B_87, C_88]: (k7_subset_1(A_86, B_87, C_88)=k4_xboole_0(B_87, C_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.53/15.69  tff(c_756, plain, (![C_91]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_91)=k4_xboole_0('#skF_2', C_91))), inference(resolution, [status(thm)], [c_44, c_683])).
% 23.53/15.69  tff(c_768, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_120, c_756])).
% 23.53/15.69  tff(c_145, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_16, c_134])).
% 23.53/15.69  tff(c_514, plain, (![A_79, B_80]: (r1_tarski(A_79, k2_xboole_0(B_80, A_79)))), inference(resolution, [status(thm)], [c_16, c_493])).
% 23.53/15.69  tff(c_544, plain, (![A_79, B_80]: (k2_xboole_0(A_79, k2_xboole_0(B_80, A_79))=k2_xboole_0(B_80, A_79))), inference(resolution, [status(thm)], [c_514, c_10])).
% 23.53/15.69  tff(c_18, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k4_xboole_0(A_12, B_13), C_14)=k4_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.53/15.69  tff(c_372, plain, (![A_69, B_70, C_71]: (k4_xboole_0(k4_xboole_0(A_69, B_70), C_71)=k4_xboole_0(A_69, k2_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.53/15.69  tff(c_375, plain, (![A_69, B_70, C_71, C_14]: (k4_xboole_0(k4_xboole_0(A_69, k2_xboole_0(B_70, C_71)), C_14)=k4_xboole_0(k4_xboole_0(A_69, B_70), k2_xboole_0(C_71, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_372, c_18])).
% 23.53/15.69  tff(c_408, plain, (![A_69, B_70, C_71, C_14]: (k4_xboole_0(A_69, k2_xboole_0(k2_xboole_0(B_70, C_71), C_14))=k4_xboole_0(A_69, k2_xboole_0(B_70, k2_xboole_0(C_71, C_14))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_375])).
% 23.53/15.69  tff(c_904, plain, (![A_96, C_14]: (k4_xboole_0(A_96, k2_xboole_0(A_96, C_14))=k4_xboole_0(k1_xboole_0, C_14))), inference(superposition, [status(thm), theory('equality')], [c_889, c_18])).
% 23.53/15.69  tff(c_1053, plain, (![A_101, C_102]: (k4_xboole_0(A_101, k2_xboole_0(A_101, C_102))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_904])).
% 23.53/15.69  tff(c_1240, plain, (![A_107, B_108]: (k4_xboole_0(k4_xboole_0(A_107, B_108), A_107)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_145, c_1053])).
% 23.53/15.69  tff(c_1301, plain, (![C_14, B_13]: (k4_xboole_0(C_14, k2_xboole_0(B_13, C_14))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_1240])).
% 23.53/15.69  tff(c_882, plain, (![A_95]: (k4_xboole_0(A_95, A_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_282, c_855])).
% 23.53/15.69  tff(c_146, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_134])).
% 23.53/15.69  tff(c_11305, plain, (![A_277, B_278, C_279]: (k4_xboole_0(k4_xboole_0(A_277, B_278), k4_xboole_0(A_277, k2_xboole_0(B_278, C_279)))=k3_xboole_0(k4_xboole_0(A_277, B_278), C_279))), inference(superposition, [status(thm), theory('equality')], [c_372, c_22])).
% 23.53/15.69  tff(c_11534, plain, (![A_277, B_4]: (k4_xboole_0(k4_xboole_0(A_277, B_4), k4_xboole_0(A_277, B_4))=k3_xboole_0(k4_xboole_0(A_277, B_4), B_4))), inference(superposition, [status(thm), theory('equality')], [c_146, c_11305])).
% 23.53/15.69  tff(c_11605, plain, (![B_280, A_281]: (k3_xboole_0(B_280, k4_xboole_0(A_281, B_280))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_882, c_2, c_11534])).
% 23.53/15.69  tff(c_102, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.53/15.69  tff(c_3268, plain, (![A_179, B_180]: (k3_xboole_0(k4_xboole_0(A_179, B_180), A_179)=k4_xboole_0(A_179, B_180))), inference(resolution, [status(thm)], [c_16, c_102])).
% 23.53/15.69  tff(c_3399, plain, (![A_1, B_180]: (k3_xboole_0(A_1, k4_xboole_0(A_1, B_180))=k4_xboole_0(A_1, B_180))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3268])).
% 23.53/15.69  tff(c_226, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k3_xboole_0(A_63, k4_xboole_0(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_223, c_22])).
% 23.53/15.69  tff(c_5110, plain, (![A_217, B_218]: (k4_xboole_0(A_217, k3_xboole_0(A_217, B_218))=k4_xboole_0(A_217, B_218))), inference(demodulation, [status(thm), theory('equality')], [c_3399, c_226])).
% 23.53/15.69  tff(c_5229, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5110])).
% 23.53/15.69  tff(c_11628, plain, (![A_281, B_280]: (k4_xboole_0(k4_xboole_0(A_281, B_280), k1_xboole_0)=k4_xboole_0(k4_xboole_0(A_281, B_280), B_280))), inference(superposition, [status(thm), theory('equality')], [c_11605, c_5229])).
% 23.53/15.69  tff(c_17668, plain, (![A_329, B_330]: (k4_xboole_0(k4_xboole_0(A_329, B_330), B_330)=k4_xboole_0(A_329, B_330))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18, c_11628])).
% 23.53/15.69  tff(c_404, plain, (![A_69, B_70, B_19]: (k4_xboole_0(A_69, k2_xboole_0(B_70, k4_xboole_0(k4_xboole_0(A_69, B_70), B_19)))=k3_xboole_0(k4_xboole_0(A_69, B_70), B_19))), inference(superposition, [status(thm), theory('equality')], [c_22, c_372])).
% 23.53/15.69  tff(c_413, plain, (![A_69, B_70, B_19]: (k4_xboole_0(A_69, k2_xboole_0(B_70, k4_xboole_0(A_69, k2_xboole_0(B_70, B_19))))=k3_xboole_0(k4_xboole_0(A_69, B_70), B_19))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_404])).
% 23.53/15.69  tff(c_17694, plain, (![A_329, B_70, B_19]: (k4_xboole_0(k4_xboole_0(A_329, k2_xboole_0(B_70, B_19)), k2_xboole_0(B_70, k4_xboole_0(A_329, k2_xboole_0(B_70, B_19))))=k3_xboole_0(k4_xboole_0(k4_xboole_0(A_329, k2_xboole_0(B_70, B_19)), B_70), B_19))), inference(superposition, [status(thm), theory('equality')], [c_17668, c_413])).
% 23.53/15.69  tff(c_40041, plain, (![B_498, A_499, B_500]: (k3_xboole_0(B_498, k4_xboole_0(A_499, k2_xboole_0(B_498, B_500)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_544, c_408, c_1301, c_18, c_2, c_17694])).
% 23.53/15.69  tff(c_60863, plain, (![A_605, B_606, A_607]: (k3_xboole_0(k4_xboole_0(A_605, B_606), k4_xboole_0(A_607, A_605))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_145, c_40041])).
% 23.53/15.69  tff(c_61482, plain, (![A_607]: (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k4_xboole_0(A_607, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_768, c_60863])).
% 23.53/15.69  tff(c_43271, plain, (![A_518, B_519, C_520]: (r1_tarski(k4_xboole_0(A_518, B_519), k2_xboole_0(C_520, k4_xboole_0(A_518, k2_xboole_0(B_519, C_520)))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_772])).
% 23.53/15.69  tff(c_43604, plain, (![B_519, C_520]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_519, C_520), B_519), k2_xboole_0(C_520, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_882, c_43271])).
% 23.53/15.69  tff(c_43740, plain, (![B_521, C_522]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_521, C_522), B_521), C_522))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_43604])).
% 23.53/15.69  tff(c_43908, plain, (![B_523, C_524]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_523, C_524), B_523), C_524)=C_524)), inference(resolution, [status(thm)], [c_43740, c_10])).
% 23.53/15.69  tff(c_939, plain, (![A_96, C_14]: (k4_xboole_0(A_96, k2_xboole_0(A_96, C_14))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_904])).
% 23.53/15.69  tff(c_44530, plain, (![B_527, C_528]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(B_527, C_528), B_527), C_528)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_43908, c_939])).
% 23.53/15.69  tff(c_44748, plain, (k4_xboole_0(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26367, c_44530])).
% 23.53/15.69  tff(c_630, plain, (![A_84, B_85]: (k2_xboole_0(k3_xboole_0(A_84, B_85), A_84)=A_84)), inference(resolution, [status(thm)], [c_339, c_10])).
% 23.53/15.69  tff(c_667, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_630])).
% 23.53/15.69  tff(c_1088, plain, (![A_1, B_2]: (k4_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_667, c_1053])).
% 23.53/15.69  tff(c_5625, plain, (![A_223, B_224, C_225]: (k4_xboole_0(A_223, k2_xboole_0(k4_xboole_0(A_223, B_224), C_225))=k4_xboole_0(k3_xboole_0(A_223, B_224), C_225))), inference(superposition, [status(thm), theory('equality')], [c_22, c_372])).
% 23.53/15.69  tff(c_513, plain, (![A_76, B_77]: (r1_tarski(A_76, k2_xboole_0(B_77, k4_xboole_0(A_76, B_77))))), inference(resolution, [status(thm)], [c_8, c_493])).
% 23.53/15.69  tff(c_71842, plain, (![A_666, B_667, C_668]: (r1_tarski(A_666, k2_xboole_0(k2_xboole_0(k4_xboole_0(A_666, B_667), C_668), k4_xboole_0(k3_xboole_0(A_666, B_667), C_668))))), inference(superposition, [status(thm), theory('equality')], [c_5625, c_513])).
% 23.53/15.69  tff(c_72345, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(k2_xboole_0(k4_xboole_0(A_1, B_2), B_2), k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1088, c_71842])).
% 23.53/15.69  tff(c_72587, plain, (![A_669, B_670]: (r1_tarski(A_669, k2_xboole_0(k4_xboole_0(A_669, B_670), B_670)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_72345])).
% 23.53/15.69  tff(c_72855, plain, (![A_669, B_670]: (k3_xboole_0(A_669, k2_xboole_0(k4_xboole_0(A_669, B_670), B_670))=A_669)), inference(resolution, [status(thm)], [c_72587, c_14])).
% 23.53/15.69  tff(c_99361, plain, (k3_xboole_0(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'), k2_xboole_0(k1_xboole_0, k2_tops_1('#skF_1', '#skF_2')))=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_44748, c_72855])).
% 23.53/15.69  tff(c_99564, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_61482, c_2, c_425, c_99361])).
% 23.53/15.69  tff(c_110, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_102])).
% 23.53/15.69  tff(c_72921, plain, (![A_671, B_672]: (k3_xboole_0(A_671, k2_xboole_0(k4_xboole_0(A_671, B_672), B_672))=A_671)), inference(resolution, [status(thm)], [c_72587, c_14])).
% 23.53/15.69  tff(c_457, plain, (![A_74, B_75]: (r1_tarski(k3_xboole_0(A_74, B_75), B_75))), inference(superposition, [status(thm), theory('equality')], [c_2, c_339])).
% 23.53/15.69  tff(c_7913, plain, (![A_250, B_251]: (k3_xboole_0(k3_xboole_0(A_250, B_251), B_251)=k3_xboole_0(A_250, B_251))), inference(resolution, [status(thm)], [c_457, c_14])).
% 23.53/15.69  tff(c_8975, plain, (![B_258, A_259]: (k3_xboole_0(k3_xboole_0(B_258, A_259), B_258)=k3_xboole_0(A_259, B_258))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7913])).
% 23.53/15.69  tff(c_9208, plain, (![A_1, A_259]: (k3_xboole_0(A_1, k3_xboole_0(A_1, A_259))=k3_xboole_0(A_259, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8975])).
% 23.53/15.69  tff(c_73150, plain, (![A_671, B_672]: (k3_xboole_0(k2_xboole_0(k4_xboole_0(A_671, B_672), B_672), A_671)=k3_xboole_0(A_671, A_671))), inference(superposition, [status(thm), theory('equality')], [c_72921, c_9208])).
% 23.53/15.69  tff(c_73624, plain, (![A_671, B_672]: (k3_xboole_0(k2_xboole_0(k4_xboole_0(A_671, B_672), B_672), A_671)=A_671)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_73150])).
% 23.53/15.69  tff(c_99653, plain, (k3_xboole_0(k2_xboole_0(k1_xboole_0, '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_99564, c_73624])).
% 23.53/15.69  tff(c_99887, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26445, c_425, c_99653])).
% 23.53/15.69  tff(c_99889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2153, c_99887])).
% 23.53/15.69  tff(c_99890, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 23.53/15.69  tff(c_100145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_99890])).
% 23.53/15.69  tff(c_100146, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 23.53/15.69  tff(c_100231, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100146, c_50])).
% 23.53/15.69  tff(c_100778, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100711, c_100231])).
% 23.53/15.69  tff(c_101613, plain, (![A_845, B_846]: (k2_pre_topc(A_845, B_846)=B_846 | ~v4_pre_topc(B_846, A_845) | ~m1_subset_1(B_846, k1_zfmisc_1(u1_struct_0(A_845))) | ~l1_pre_topc(A_845))), inference(cnfTransformation, [status(thm)], [f_82])).
% 23.53/15.69  tff(c_101623, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_101613])).
% 23.53/15.69  tff(c_101628, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_100146, c_101623])).
% 23.53/15.69  tff(c_103152, plain, (![A_904, B_905]: (k7_subset_1(u1_struct_0(A_904), k2_pre_topc(A_904, B_905), k1_tops_1(A_904, B_905))=k2_tops_1(A_904, B_905) | ~m1_subset_1(B_905, k1_zfmisc_1(u1_struct_0(A_904))) | ~l1_pre_topc(A_904))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.53/15.69  tff(c_103161, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_101628, c_103152])).
% 23.53/15.69  tff(c_103165, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_100711, c_103161])).
% 23.53/15.69  tff(c_103167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100778, c_103165])).
% 23.53/15.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.53/15.69  
% 23.53/15.69  Inference rules
% 23.53/15.69  ----------------------
% 23.53/15.69  #Ref     : 0
% 23.53/15.69  #Sup     : 25198
% 23.53/15.69  #Fact    : 0
% 23.53/15.69  #Define  : 0
% 23.53/15.69  #Split   : 6
% 23.53/15.69  #Chain   : 0
% 23.53/15.69  #Close   : 0
% 23.53/15.69  
% 23.53/15.69  Ordering : KBO
% 23.53/15.69  
% 23.53/15.69  Simplification rules
% 23.53/15.69  ----------------------
% 23.53/15.69  #Subsume      : 492
% 23.53/15.69  #Demod        : 31147
% 23.53/15.69  #Tautology    : 18014
% 23.53/15.69  #SimpNegUnit  : 9
% 23.53/15.69  #BackRed      : 9
% 23.53/15.69  
% 23.53/15.69  #Partial instantiations: 0
% 23.53/15.69  #Strategies tried      : 1
% 23.53/15.69  
% 23.53/15.69  Timing (in seconds)
% 23.53/15.69  ----------------------
% 23.53/15.69  Preprocessing        : 0.33
% 23.53/15.69  Parsing              : 0.18
% 23.53/15.69  CNF conversion       : 0.02
% 23.53/15.69  Main loop            : 14.57
% 23.53/15.69  Inferencing          : 1.58
% 23.53/15.69  Reduction            : 9.52
% 23.53/15.69  Demodulation         : 8.68
% 23.53/15.69  BG Simplification    : 0.17
% 23.53/15.69  Subsumption          : 2.73
% 23.53/15.70  Abstraction          : 0.34
% 23.53/15.70  MUC search           : 0.00
% 23.53/15.70  Cooper               : 0.00
% 23.53/15.70  Total                : 14.96
% 23.53/15.70  Index Insertion      : 0.00
% 23.53/15.70  Index Deletion       : 0.00
% 23.53/15.70  Index Matching       : 0.00
% 23.53/15.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
