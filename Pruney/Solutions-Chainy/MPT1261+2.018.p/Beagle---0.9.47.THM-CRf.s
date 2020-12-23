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
% DateTime   : Thu Dec  3 10:21:14 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 148 expanded)
%              Number of leaves         :   40 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 281 expanded)
%              Number of equality atoms :   61 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_65,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_67,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2682,plain,(
    ! [A_192,B_193,C_194] :
      ( k7_subset_1(A_192,B_193,C_194) = k4_xboole_0(B_193,C_194)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(A_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2685,plain,(
    ! [C_194] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_194) = k4_xboole_0('#skF_2',C_194) ),
    inference(resolution,[status(thm)],[c_42,c_2682])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_296,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1092,plain,(
    ! [B_103,A_104] :
      ( v4_pre_topc(B_103,A_104)
      | k2_pre_topc(A_104,B_103) != B_103
      | ~ v2_pre_topc(A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1108,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1092])).

tff(c_1122,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_1108])).

tff(c_1123,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_1122])).

tff(c_1191,plain,(
    ! [A_109,B_110] :
      ( k4_subset_1(u1_struct_0(A_109),B_110,k2_tops_1(A_109,B_110)) = k2_pre_topc(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1202,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1191])).

tff(c_1215,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1202])).

tff(c_20,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_232,plain,(
    ! [A_55,B_56] : k1_setfam_1(k2_tarski(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_273,plain,(
    ! [B_59,A_60] : k1_setfam_1(k2_tarski(B_59,A_60)) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_232])).

tff(c_32,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_297,plain,(
    ! [B_61,A_62] : k3_xboole_0(B_61,A_62) = k3_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_32])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_215,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_231,plain,(
    ! [A_9] : k3_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_215])).

tff(c_313,plain,(
    ! [B_61] : k3_xboole_0(B_61,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_231])).

tff(c_389,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_398,plain,(
    ! [B_61] : k5_xboole_0(B_61,k1_xboole_0) = k4_xboole_0(B_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_389])).

tff(c_413,plain,(
    ! [B_61] : k5_xboole_0(B_61,k1_xboole_0) = B_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_398])).

tff(c_595,plain,(
    ! [A_76,B_77,C_78] :
      ( k7_subset_1(A_76,B_77,C_78) = k4_xboole_0(B_77,C_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_696,plain,(
    ! [C_85] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_85) = k4_xboole_0('#skF_2',C_85) ),
    inference(resolution,[status(thm)],[c_42,c_595])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_106,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_702,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_106])).

tff(c_18,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_107])).

tff(c_762,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_121])).

tff(c_22,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_794,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_22])).

tff(c_806,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_794])).

tff(c_26,plain,(
    ! [A_17,B_18,C_19] :
      ( m1_subset_1(k7_subset_1(A_17,B_18,C_19),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_965,plain,(
    ! [A_97,B_98,C_99] :
      ( k4_subset_1(A_97,B_98,C_99) = k2_xboole_0(B_98,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1789,plain,(
    ! [A_141,B_142,B_143,C_144] :
      ( k4_subset_1(A_141,B_142,k7_subset_1(A_141,B_143,C_144)) = k2_xboole_0(B_142,k7_subset_1(A_141,B_143,C_144))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_141))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(A_141)) ) ),
    inference(resolution,[status(thm)],[c_26,c_965])).

tff(c_1856,plain,(
    ! [B_146,C_147] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k7_subset_1(u1_struct_0('#skF_1'),B_146,C_147)) = k2_xboole_0('#skF_2',k7_subset_1(u1_struct_0('#skF_1'),B_146,C_147))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_42,c_1789])).

tff(c_1881,plain,
    ( k2_xboole_0('#skF_2',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_1856])).

tff(c_1895,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1215,c_806,c_106,c_1881])).

tff(c_1897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1123,c_1895])).

tff(c_1898,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1898,c_106])).

tff(c_2195,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2364,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2195,c_48])).

tff(c_2783,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2364])).

tff(c_2951,plain,(
    ! [A_213,B_214] :
      ( k2_pre_topc(A_213,B_214) = B_214
      | ~ v4_pre_topc(B_214,A_213)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2964,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2951])).

tff(c_2974,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2195,c_2964])).

tff(c_3655,plain,(
    ! [A_260,B_261] :
      ( k7_subset_1(u1_struct_0(A_260),k2_pre_topc(A_260,B_261),k1_tops_1(A_260,B_261)) = k2_tops_1(A_260,B_261)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ l1_pre_topc(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3671,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2974,c_3655])).

tff(c_3677,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2685,c_3671])).

tff(c_3679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2783,c_3677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.95  
% 4.34/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.96  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.34/1.96  
% 4.34/1.96  %Foreground sorts:
% 4.34/1.96  
% 4.34/1.96  
% 4.34/1.96  %Background operators:
% 4.34/1.96  
% 4.34/1.96  
% 4.34/1.96  %Foreground operators:
% 4.34/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.34/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.34/1.96  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.34/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.34/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.34/1.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.34/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.34/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.34/1.96  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.34/1.96  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.34/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.34/1.96  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.34/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.34/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.34/1.96  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.34/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.34/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.34/1.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.34/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.34/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.34/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.34/1.96  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.34/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.34/1.96  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.34/1.96  
% 4.34/1.97  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.34/1.97  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.34/1.97  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.34/1.97  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.34/1.97  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.34/1.97  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.34/1.97  tff(f_67, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.34/1.97  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.34/1.97  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.34/1.97  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.34/1.97  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.34/1.97  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.34/1.97  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.34/1.97  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.34/1.97  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.34/1.97  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.34/1.97  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.34/1.97  tff(c_2682, plain, (![A_192, B_193, C_194]: (k7_subset_1(A_192, B_193, C_194)=k4_xboole_0(B_193, C_194) | ~m1_subset_1(B_193, k1_zfmisc_1(A_192)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.34/1.97  tff(c_2685, plain, (![C_194]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_194)=k4_xboole_0('#skF_2', C_194))), inference(resolution, [status(thm)], [c_42, c_2682])).
% 4.34/1.97  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.34/1.97  tff(c_296, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 4.34/1.97  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.34/1.97  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.34/1.97  tff(c_1092, plain, (![B_103, A_104]: (v4_pre_topc(B_103, A_104) | k2_pre_topc(A_104, B_103)!=B_103 | ~v2_pre_topc(A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.34/1.97  tff(c_1108, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1092])).
% 4.34/1.97  tff(c_1122, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_1108])).
% 4.34/1.97  tff(c_1123, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_296, c_1122])).
% 4.34/1.97  tff(c_1191, plain, (![A_109, B_110]: (k4_subset_1(u1_struct_0(A_109), B_110, k2_tops_1(A_109, B_110))=k2_pre_topc(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.34/1.97  tff(c_1202, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1191])).
% 4.34/1.97  tff(c_1215, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1202])).
% 4.34/1.97  tff(c_20, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.34/1.97  tff(c_24, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.34/1.97  tff(c_232, plain, (![A_55, B_56]: (k1_setfam_1(k2_tarski(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.34/1.97  tff(c_273, plain, (![B_59, A_60]: (k1_setfam_1(k2_tarski(B_59, A_60))=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_24, c_232])).
% 4.34/1.97  tff(c_32, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.34/1.97  tff(c_297, plain, (![B_61, A_62]: (k3_xboole_0(B_61, A_62)=k3_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_273, c_32])).
% 4.34/1.97  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.34/1.97  tff(c_215, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.34/1.97  tff(c_231, plain, (![A_9]: (k3_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_215])).
% 4.34/1.97  tff(c_313, plain, (![B_61]: (k3_xboole_0(B_61, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_297, c_231])).
% 4.34/1.97  tff(c_389, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.34/1.97  tff(c_398, plain, (![B_61]: (k5_xboole_0(B_61, k1_xboole_0)=k4_xboole_0(B_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_313, c_389])).
% 4.34/1.97  tff(c_413, plain, (![B_61]: (k5_xboole_0(B_61, k1_xboole_0)=B_61)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_398])).
% 4.34/1.97  tff(c_595, plain, (![A_76, B_77, C_78]: (k7_subset_1(A_76, B_77, C_78)=k4_xboole_0(B_77, C_78) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.34/1.97  tff(c_696, plain, (![C_85]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_85)=k4_xboole_0('#skF_2', C_85))), inference(resolution, [status(thm)], [c_42, c_595])).
% 4.34/1.97  tff(c_54, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.34/1.97  tff(c_106, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 4.34/1.97  tff(c_702, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_696, c_106])).
% 4.34/1.97  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.34/1.97  tff(c_107, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.34/1.97  tff(c_121, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_107])).
% 4.34/1.97  tff(c_762, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_702, c_121])).
% 4.34/1.97  tff(c_22, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.34/1.97  tff(c_794, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_762, c_22])).
% 4.34/1.97  tff(c_806, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_413, c_794])).
% 4.34/1.97  tff(c_26, plain, (![A_17, B_18, C_19]: (m1_subset_1(k7_subset_1(A_17, B_18, C_19), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.34/1.97  tff(c_965, plain, (![A_97, B_98, C_99]: (k4_subset_1(A_97, B_98, C_99)=k2_xboole_0(B_98, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(A_97)) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.34/1.97  tff(c_1789, plain, (![A_141, B_142, B_143, C_144]: (k4_subset_1(A_141, B_142, k7_subset_1(A_141, B_143, C_144))=k2_xboole_0(B_142, k7_subset_1(A_141, B_143, C_144)) | ~m1_subset_1(B_142, k1_zfmisc_1(A_141)) | ~m1_subset_1(B_143, k1_zfmisc_1(A_141)))), inference(resolution, [status(thm)], [c_26, c_965])).
% 4.34/1.97  tff(c_1856, plain, (![B_146, C_147]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k7_subset_1(u1_struct_0('#skF_1'), B_146, C_147))=k2_xboole_0('#skF_2', k7_subset_1(u1_struct_0('#skF_1'), B_146, C_147)) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_42, c_1789])).
% 4.34/1.97  tff(c_1881, plain, (k2_xboole_0('#skF_2', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_106, c_1856])).
% 4.34/1.97  tff(c_1895, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1215, c_806, c_106, c_1881])).
% 4.34/1.97  tff(c_1897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1123, c_1895])).
% 4.34/1.97  tff(c_1898, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 4.34/1.97  tff(c_2194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1898, c_106])).
% 4.34/1.97  tff(c_2195, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 4.34/1.97  tff(c_2364, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2195, c_48])).
% 4.34/1.97  tff(c_2783, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2364])).
% 4.34/1.97  tff(c_2951, plain, (![A_213, B_214]: (k2_pre_topc(A_213, B_214)=B_214 | ~v4_pre_topc(B_214, A_213) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.34/1.97  tff(c_2964, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2951])).
% 4.34/1.97  tff(c_2974, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2195, c_2964])).
% 4.34/1.97  tff(c_3655, plain, (![A_260, B_261]: (k7_subset_1(u1_struct_0(A_260), k2_pre_topc(A_260, B_261), k1_tops_1(A_260, B_261))=k2_tops_1(A_260, B_261) | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0(A_260))) | ~l1_pre_topc(A_260))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.34/1.97  tff(c_3671, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2974, c_3655])).
% 4.34/1.97  tff(c_3677, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2685, c_3671])).
% 4.34/1.97  tff(c_3679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2783, c_3677])).
% 4.34/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.97  
% 4.34/1.97  Inference rules
% 4.34/1.97  ----------------------
% 4.34/1.97  #Ref     : 0
% 4.34/1.97  #Sup     : 838
% 4.34/1.97  #Fact    : 0
% 4.34/1.97  #Define  : 0
% 4.34/1.97  #Split   : 7
% 4.34/1.97  #Chain   : 0
% 4.34/1.97  #Close   : 0
% 4.34/1.97  
% 4.34/1.97  Ordering : KBO
% 4.34/1.97  
% 4.34/1.97  Simplification rules
% 4.34/1.97  ----------------------
% 4.34/1.97  #Subsume      : 27
% 4.34/1.97  #Demod        : 687
% 4.34/1.97  #Tautology    : 604
% 4.34/1.97  #SimpNegUnit  : 14
% 4.34/1.97  #BackRed      : 1
% 4.34/1.97  
% 4.34/1.97  #Partial instantiations: 0
% 4.34/1.97  #Strategies tried      : 1
% 4.34/1.97  
% 4.34/1.97  Timing (in seconds)
% 4.34/1.97  ----------------------
% 4.34/1.98  Preprocessing        : 0.33
% 4.34/1.98  Parsing              : 0.17
% 4.34/1.98  CNF conversion       : 0.02
% 4.34/1.98  Main loop            : 0.75
% 4.34/1.98  Inferencing          : 0.27
% 4.34/1.98  Reduction            : 0.28
% 4.34/1.98  Demodulation         : 0.22
% 4.34/1.98  BG Simplification    : 0.03
% 4.34/1.98  Subsumption          : 0.11
% 4.34/1.98  Abstraction          : 0.05
% 4.34/1.98  MUC search           : 0.00
% 4.34/1.98  Cooper               : 0.00
% 4.34/1.98  Total                : 1.12
% 4.34/1.98  Index Insertion      : 0.00
% 4.34/1.98  Index Deletion       : 0.00
% 4.34/1.98  Index Matching       : 0.00
% 4.34/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
