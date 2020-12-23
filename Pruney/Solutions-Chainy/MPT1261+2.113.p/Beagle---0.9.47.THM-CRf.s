%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:27 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 5.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 215 expanded)
%              Number of leaves         :   40 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :  160 ( 435 expanded)
%              Number of equality atoms :   63 ( 138 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2682,plain,(
    ! [A_218,B_219,C_220] :
      ( k7_subset_1(A_218,B_219,C_220) = k4_xboole_0(B_219,C_220)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(A_218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2691,plain,(
    ! [C_220] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_220) = k4_xboole_0('#skF_2',C_220) ),
    inference(resolution,[status(thm)],[c_40,c_2682])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_111,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_182,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_989,plain,(
    ! [B_117,A_118] :
      ( v4_pre_topc(B_117,A_118)
      | k2_pre_topc(A_118,B_117) != B_117
      | ~ v2_pre_topc(A_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1003,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_989])).

tff(c_1009,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1003])).

tff(c_1010,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_1009])).

tff(c_280,plain,(
    ! [A_73,B_74,C_75] :
      ( k7_subset_1(A_73,B_74,C_75) = k4_xboole_0(B_74,C_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_290,plain,(
    ! [C_76] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_76) = k4_xboole_0('#skF_2',C_76) ),
    inference(resolution,[status(thm)],[c_40,c_280])).

tff(c_296,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_111])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_320,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_6])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k3_subset_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_717,plain,(
    ! [A_108,B_109,C_110] :
      ( k4_subset_1(A_108,B_109,C_110) = k2_xboole_0(B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(A_108))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2099,plain,(
    ! [A_172,B_173,B_174] :
      ( k4_subset_1(A_172,B_173,k3_subset_1(A_172,B_174)) = k2_xboole_0(B_173,k3_subset_1(A_172,B_174))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(A_172))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_172)) ) ),
    inference(resolution,[status(thm)],[c_14,c_717])).

tff(c_2399,plain,(
    ! [B_188,A_189,B_190] :
      ( k4_subset_1(B_188,A_189,k3_subset_1(B_188,B_190)) = k2_xboole_0(A_189,k3_subset_1(B_188,B_190))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(B_188))
      | ~ r1_tarski(A_189,B_188) ) ),
    inference(resolution,[status(thm)],[c_26,c_2099])).

tff(c_2412,plain,(
    ! [B_191,A_192,A_193] :
      ( k4_subset_1(B_191,A_192,k3_subset_1(B_191,A_193)) = k2_xboole_0(A_192,k3_subset_1(B_191,A_193))
      | ~ r1_tarski(A_192,B_191)
      | ~ r1_tarski(A_193,B_191) ) ),
    inference(resolution,[status(thm)],[c_26,c_2399])).

tff(c_10,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k4_subset_1(A_20,B_21,k3_subset_1(A_20,B_21)) = k2_subset_1(A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_230,plain,(
    ! [A_67,B_68] :
      ( k4_subset_1(A_67,B_68,k3_subset_1(A_67,B_68)) = A_67
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_238,plain,(
    ! [B_25,A_24] :
      ( k4_subset_1(B_25,A_24,k3_subset_1(B_25,A_24)) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_230])).

tff(c_2494,plain,(
    ! [A_194,B_195] :
      ( k2_xboole_0(A_194,k3_subset_1(B_195,A_194)) = B_195
      | ~ r1_tarski(A_194,B_195)
      | ~ r1_tarski(A_194,B_195)
      | ~ r1_tarski(A_194,B_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2412,c_238])).

tff(c_1232,plain,(
    ! [A_127,B_128] :
      ( k4_subset_1(u1_struct_0(A_127),B_128,k2_tops_1(A_127,B_128)) = k2_pre_topc(A_127,B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1242,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1232])).

tff(c_1248,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1242])).

tff(c_589,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(k2_tops_1(A_96,B_97),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_610,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(k2_tops_1(A_96,B_97),u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_589,c_24])).

tff(c_892,plain,(
    ! [B_113,B_114,A_115] :
      ( k4_subset_1(B_113,B_114,A_115) = k2_xboole_0(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(B_113))
      | ~ r1_tarski(A_115,B_113) ) ),
    inference(resolution,[status(thm)],[c_26,c_717])).

tff(c_905,plain,(
    ! [A_116] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_116) = k2_xboole_0('#skF_2',A_116)
      | ~ r1_tarski(A_116,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_892])).

tff(c_920,plain,(
    ! [B_97] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_97)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_97))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_610,c_905])).

tff(c_2076,plain,(
    ! [B_171] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_171)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_171))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_920])).

tff(c_2091,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_2076])).

tff(c_2098,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_2091])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_141,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_164,plain,(
    ! [B_61,A_62] :
      ( k4_xboole_0(B_61,A_62) = k3_subset_1(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_26,c_141])).

tff(c_191,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_subset_1(A_63,k4_xboole_0(A_63,B_64)) ),
    inference(resolution,[status(thm)],[c_6,c_164])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_200,plain,(
    ! [A_63,B_64] : k2_xboole_0(k4_xboole_0(A_63,B_64),k3_subset_1(A_63,k4_xboole_0(A_63,B_64))) = k2_xboole_0(k4_xboole_0(A_63,B_64),A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_8])).

tff(c_1253,plain,(
    ! [A_129,B_130] : k2_xboole_0(k4_xboole_0(A_129,B_130),k3_subset_1(A_129,k4_xboole_0(A_129,B_130))) = k2_xboole_0(A_129,k4_xboole_0(A_129,B_130)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_200])).

tff(c_1286,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')))) = k2_xboole_0('#skF_2',k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_1253])).

tff(c_1310,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_296,c_1286])).

tff(c_2113,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2098,c_1310])).

tff(c_2500,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2494,c_2113])).

tff(c_2529,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_320,c_320,c_2500])).

tff(c_2531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1010,c_2529])).

tff(c_2532,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2532])).

tff(c_2540,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2548,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_46])).

tff(c_2692,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2691,c_2548])).

tff(c_2802,plain,(
    ! [A_234,B_235] :
      ( k2_pre_topc(A_234,B_235) = B_235
      | ~ v4_pre_topc(B_235,A_234)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2813,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2802])).

tff(c_2818,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2540,c_2813])).

tff(c_3635,plain,(
    ! [A_282,B_283] :
      ( k7_subset_1(u1_struct_0(A_282),k2_pre_topc(A_282,B_283),k1_tops_1(A_282,B_283)) = k2_tops_1(A_282,B_283)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3644,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2818,c_3635])).

tff(c_3648,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2691,c_3644])).

tff(c_3650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2692,c_3648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.95  
% 4.92/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.96  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 4.92/1.96  
% 4.92/1.96  %Foreground sorts:
% 4.92/1.96  
% 4.92/1.96  
% 4.92/1.96  %Background operators:
% 4.92/1.96  
% 4.92/1.96  
% 4.92/1.96  %Foreground operators:
% 4.92/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.92/1.96  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.92/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.92/1.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.92/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.92/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.92/1.96  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.92/1.96  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.92/1.96  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.92/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.92/1.96  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.92/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.92/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.92/1.96  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.92/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.92/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.92/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.92/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.92/1.96  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.92/1.96  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.92/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.92/1.96  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.92/1.96  
% 5.21/1.97  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.21/1.97  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.21/1.97  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.21/1.97  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.21/1.97  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.21/1.97  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.21/1.97  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.21/1.97  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.21/1.97  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 5.21/1.97  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.21/1.97  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.21/1.97  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.21/1.97  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.21/1.97  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.21/1.97  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.21/1.97  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.21/1.97  tff(c_2682, plain, (![A_218, B_219, C_220]: (k7_subset_1(A_218, B_219, C_220)=k4_xboole_0(B_219, C_220) | ~m1_subset_1(B_219, k1_zfmisc_1(A_218)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.21/1.97  tff(c_2691, plain, (![C_220]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_220)=k4_xboole_0('#skF_2', C_220))), inference(resolution, [status(thm)], [c_40, c_2682])).
% 5.21/1.97  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.21/1.97  tff(c_111, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 5.21/1.97  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.21/1.97  tff(c_182, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 5.21/1.97  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.21/1.97  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.21/1.97  tff(c_989, plain, (![B_117, A_118]: (v4_pre_topc(B_117, A_118) | k2_pre_topc(A_118, B_117)!=B_117 | ~v2_pre_topc(A_118) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.21/1.97  tff(c_1003, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_989])).
% 5.21/1.97  tff(c_1009, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1003])).
% 5.21/1.97  tff(c_1010, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_182, c_1009])).
% 5.21/1.97  tff(c_280, plain, (![A_73, B_74, C_75]: (k7_subset_1(A_73, B_74, C_75)=k4_xboole_0(B_74, C_75) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.21/1.97  tff(c_290, plain, (![C_76]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_76)=k4_xboole_0('#skF_2', C_76))), inference(resolution, [status(thm)], [c_40, c_280])).
% 5.21/1.97  tff(c_296, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_290, c_111])).
% 5.21/1.97  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.21/1.97  tff(c_320, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_296, c_6])).
% 5.21/1.97  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.21/1.97  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(k3_subset_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.21/1.97  tff(c_717, plain, (![A_108, B_109, C_110]: (k4_subset_1(A_108, B_109, C_110)=k2_xboole_0(B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(A_108)) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.21/1.97  tff(c_2099, plain, (![A_172, B_173, B_174]: (k4_subset_1(A_172, B_173, k3_subset_1(A_172, B_174))=k2_xboole_0(B_173, k3_subset_1(A_172, B_174)) | ~m1_subset_1(B_173, k1_zfmisc_1(A_172)) | ~m1_subset_1(B_174, k1_zfmisc_1(A_172)))), inference(resolution, [status(thm)], [c_14, c_717])).
% 5.21/1.97  tff(c_2399, plain, (![B_188, A_189, B_190]: (k4_subset_1(B_188, A_189, k3_subset_1(B_188, B_190))=k2_xboole_0(A_189, k3_subset_1(B_188, B_190)) | ~m1_subset_1(B_190, k1_zfmisc_1(B_188)) | ~r1_tarski(A_189, B_188))), inference(resolution, [status(thm)], [c_26, c_2099])).
% 5.21/1.97  tff(c_2412, plain, (![B_191, A_192, A_193]: (k4_subset_1(B_191, A_192, k3_subset_1(B_191, A_193))=k2_xboole_0(A_192, k3_subset_1(B_191, A_193)) | ~r1_tarski(A_192, B_191) | ~r1_tarski(A_193, B_191))), inference(resolution, [status(thm)], [c_26, c_2399])).
% 5.21/1.97  tff(c_10, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.21/1.97  tff(c_20, plain, (![A_20, B_21]: (k4_subset_1(A_20, B_21, k3_subset_1(A_20, B_21))=k2_subset_1(A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.21/1.97  tff(c_230, plain, (![A_67, B_68]: (k4_subset_1(A_67, B_68, k3_subset_1(A_67, B_68))=A_67 | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 5.21/1.97  tff(c_238, plain, (![B_25, A_24]: (k4_subset_1(B_25, A_24, k3_subset_1(B_25, A_24))=B_25 | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_230])).
% 5.21/1.97  tff(c_2494, plain, (![A_194, B_195]: (k2_xboole_0(A_194, k3_subset_1(B_195, A_194))=B_195 | ~r1_tarski(A_194, B_195) | ~r1_tarski(A_194, B_195) | ~r1_tarski(A_194, B_195))), inference(superposition, [status(thm), theory('equality')], [c_2412, c_238])).
% 5.21/1.97  tff(c_1232, plain, (![A_127, B_128]: (k4_subset_1(u1_struct_0(A_127), B_128, k2_tops_1(A_127, B_128))=k2_pre_topc(A_127, B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.21/1.97  tff(c_1242, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1232])).
% 5.21/1.97  tff(c_1248, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1242])).
% 5.21/1.97  tff(c_589, plain, (![A_96, B_97]: (m1_subset_1(k2_tops_1(A_96, B_97), k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.21/1.97  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.21/1.97  tff(c_610, plain, (![A_96, B_97]: (r1_tarski(k2_tops_1(A_96, B_97), u1_struct_0(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_589, c_24])).
% 5.21/1.97  tff(c_892, plain, (![B_113, B_114, A_115]: (k4_subset_1(B_113, B_114, A_115)=k2_xboole_0(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(B_113)) | ~r1_tarski(A_115, B_113))), inference(resolution, [status(thm)], [c_26, c_717])).
% 5.21/1.97  tff(c_905, plain, (![A_116]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_116)=k2_xboole_0('#skF_2', A_116) | ~r1_tarski(A_116, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_892])).
% 5.21/1.97  tff(c_920, plain, (![B_97]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_97))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_97)) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_610, c_905])).
% 5.21/1.97  tff(c_2076, plain, (![B_171]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_171))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_171)) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_920])).
% 5.21/1.97  tff(c_2091, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_2076])).
% 5.21/1.97  tff(c_2098, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_2091])).
% 5.21/1.97  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.21/1.97  tff(c_141, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.21/1.97  tff(c_164, plain, (![B_61, A_62]: (k4_xboole_0(B_61, A_62)=k3_subset_1(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(resolution, [status(thm)], [c_26, c_141])).
% 5.21/1.97  tff(c_191, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_subset_1(A_63, k4_xboole_0(A_63, B_64)))), inference(resolution, [status(thm)], [c_6, c_164])).
% 5.21/1.97  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.21/1.97  tff(c_200, plain, (![A_63, B_64]: (k2_xboole_0(k4_xboole_0(A_63, B_64), k3_subset_1(A_63, k4_xboole_0(A_63, B_64)))=k2_xboole_0(k4_xboole_0(A_63, B_64), A_63))), inference(superposition, [status(thm), theory('equality')], [c_191, c_8])).
% 5.21/1.97  tff(c_1253, plain, (![A_129, B_130]: (k2_xboole_0(k4_xboole_0(A_129, B_130), k3_subset_1(A_129, k4_xboole_0(A_129, B_130)))=k2_xboole_0(A_129, k4_xboole_0(A_129, B_130)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_200])).
% 5.21/1.97  tff(c_1286, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))))=k2_xboole_0('#skF_2', k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_296, c_1253])).
% 5.21/1.97  tff(c_1310, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_296, c_1286])).
% 5.21/1.97  tff(c_2113, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2098, c_1310])).
% 5.21/1.97  tff(c_2500, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2494, c_2113])).
% 5.21/1.97  tff(c_2529, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_320, c_320, c_320, c_2500])).
% 5.21/1.97  tff(c_2531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1010, c_2529])).
% 5.21/1.97  tff(c_2532, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.21/1.97  tff(c_2539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_2532])).
% 5.21/1.97  tff(c_2540, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 5.21/1.97  tff(c_2548, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_46])).
% 5.21/1.97  tff(c_2692, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2691, c_2548])).
% 5.21/1.97  tff(c_2802, plain, (![A_234, B_235]: (k2_pre_topc(A_234, B_235)=B_235 | ~v4_pre_topc(B_235, A_234) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.21/1.97  tff(c_2813, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2802])).
% 5.21/1.97  tff(c_2818, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2540, c_2813])).
% 5.21/1.97  tff(c_3635, plain, (![A_282, B_283]: (k7_subset_1(u1_struct_0(A_282), k2_pre_topc(A_282, B_283), k1_tops_1(A_282, B_283))=k2_tops_1(A_282, B_283) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.21/1.97  tff(c_3644, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2818, c_3635])).
% 5.21/1.97  tff(c_3648, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2691, c_3644])).
% 5.21/1.97  tff(c_3650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2692, c_3648])).
% 5.21/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.21/1.97  
% 5.21/1.97  Inference rules
% 5.21/1.97  ----------------------
% 5.21/1.97  #Ref     : 0
% 5.21/1.97  #Sup     : 869
% 5.21/1.97  #Fact    : 0
% 5.21/1.97  #Define  : 0
% 5.21/1.97  #Split   : 3
% 5.21/1.97  #Chain   : 0
% 5.21/1.97  #Close   : 0
% 5.21/1.97  
% 5.21/1.97  Ordering : KBO
% 5.21/1.97  
% 5.21/1.97  Simplification rules
% 5.21/1.97  ----------------------
% 5.21/1.97  #Subsume      : 19
% 5.21/1.97  #Demod        : 403
% 5.21/1.97  #Tautology    : 302
% 5.21/1.97  #SimpNegUnit  : 5
% 5.21/1.97  #BackRed      : 7
% 5.21/1.97  
% 5.21/1.97  #Partial instantiations: 0
% 5.21/1.97  #Strategies tried      : 1
% 5.21/1.97  
% 5.21/1.97  Timing (in seconds)
% 5.21/1.97  ----------------------
% 5.21/1.98  Preprocessing        : 0.32
% 5.21/1.98  Parsing              : 0.17
% 5.21/1.98  CNF conversion       : 0.02
% 5.21/1.98  Main loop            : 0.85
% 5.21/1.98  Inferencing          : 0.28
% 5.21/1.98  Reduction            : 0.32
% 5.21/1.98  Demodulation         : 0.24
% 5.21/1.98  BG Simplification    : 0.04
% 5.21/1.98  Subsumption          : 0.13
% 5.21/1.98  Abstraction          : 0.06
% 5.21/1.98  MUC search           : 0.00
% 5.21/1.98  Cooper               : 0.00
% 5.21/1.98  Total                : 1.20
% 5.21/1.98  Index Insertion      : 0.00
% 5.21/1.98  Index Deletion       : 0.00
% 5.21/1.98  Index Matching       : 0.00
% 5.21/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
