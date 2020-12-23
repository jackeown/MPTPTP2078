%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:25 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 174 expanded)
%              Number of leaves         :   39 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 314 expanded)
%              Number of equality atoms :   54 ( 102 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
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

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6544,plain,(
    ! [A_276,B_277,C_278] :
      ( k7_subset_1(A_276,B_277,C_278) = k4_xboole_0(B_277,C_278)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(A_276)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6552,plain,(
    ! [C_278] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_278) = k4_xboole_0('#skF_2',C_278) ),
    inference(resolution,[status(thm)],[c_42,c_6544])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_224,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1245,plain,(
    ! [B_134,A_135] :
      ( v4_pre_topc(B_134,A_135)
      | k2_pre_topc(A_135,B_134) != B_134
      | ~ v2_pre_topc(A_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1252,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1245])).

tff(c_1260,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_1252])).

tff(c_1261,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_1260])).

tff(c_1474,plain,(
    ! [A_142,B_143] :
      ( k4_subset_1(u1_struct_0(A_142),B_143,k2_tops_1(A_142,B_143)) = k2_pre_topc(A_142,B_143)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1479,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1474])).

tff(c_1486,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1479])).

tff(c_516,plain,(
    ! [A_87,B_88,C_89] :
      ( k7_subset_1(A_87,B_88,C_89) = k4_xboole_0(B_88,C_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_562,plain,(
    ! [C_92] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_92) = k4_xboole_0('#skF_2',C_92) ),
    inference(resolution,[status(thm)],[c_42,c_516])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_142,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_568,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_142])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_175,plain,(
    ! [A_59,B_60] :
      ( k2_xboole_0(A_59,B_60) = B_60
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_201,plain,(
    ! [A_62,B_63] : k2_xboole_0(k4_xboole_0(A_62,B_63),A_62) = A_62 ),
    inference(resolution,[status(thm)],[c_14,c_175])).

tff(c_221,plain,(
    ! [A_1,B_63] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_63)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_201])).

tff(c_695,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_221])).

tff(c_153,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_165,plain,(
    ! [A_14,B_15] : k3_xboole_0(k4_xboole_0(A_14,B_15),A_14) = k4_xboole_0(A_14,B_15) ),
    inference(resolution,[status(thm)],[c_14,c_153])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_143,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_150,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_143])).

tff(c_163,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_150,c_153])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_297,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k3_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_312,plain,(
    ! [A_71,B_72] : r1_tarski(k3_xboole_0(A_71,B_72),A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_14])).

tff(c_374,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_tarski(A_77,C_78)
      | ~ r1_tarski(B_79,C_78)
      | ~ r1_tarski(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_791,plain,(
    ! [A_104,A_105,B_106] :
      ( r1_tarski(A_104,A_105)
      | ~ r1_tarski(A_104,k4_xboole_0(A_105,B_106)) ) ),
    inference(resolution,[status(thm)],[c_14,c_374])).

tff(c_822,plain,(
    ! [A_107,B_108,B_109] : r1_tarski(k3_xboole_0(k4_xboole_0(A_107,B_108),B_109),A_107) ),
    inference(resolution,[status(thm)],[c_312,c_791])).

tff(c_966,plain,(
    ! [A_117,B_118,B_119] : r1_tarski(k3_xboole_0(k3_xboole_0(A_117,B_118),B_119),A_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_822])).

tff(c_1168,plain,(
    ! [B_130,A_131,B_132] : r1_tarski(k3_xboole_0(k3_xboole_0(B_130,A_131),B_132),A_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_966])).

tff(c_1217,plain,(
    ! [B_133] : r1_tarski(k3_xboole_0('#skF_2',B_133),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1168])).

tff(c_1263,plain,(
    ! [B_136] : r1_tarski(k3_xboole_0(B_136,'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1217])).

tff(c_1381,plain,(
    ! [B_138] : r1_tarski(k4_xboole_0('#skF_2',B_138),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_1263])).

tff(c_1394,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_1381])).

tff(c_30,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_780,plain,(
    ! [A_101,B_102,C_103] :
      ( k4_subset_1(A_101,B_102,C_103) = k2_xboole_0(B_102,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_101))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5845,plain,(
    ! [B_218,B_219,A_220] :
      ( k4_subset_1(B_218,B_219,A_220) = k2_xboole_0(B_219,A_220)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(B_218))
      | ~ r1_tarski(A_220,B_218) ) ),
    inference(resolution,[status(thm)],[c_30,c_780])).

tff(c_5858,plain,(
    ! [A_221] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_221) = k2_xboole_0('#skF_2',A_221)
      | ~ r1_tarski(A_221,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_5845])).

tff(c_5876,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1394,c_5858])).

tff(c_5944,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_695,c_5876])).

tff(c_5946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1261,c_5944])).

tff(c_5947,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5947,c_142])).

tff(c_6172,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6233,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6172,c_48])).

tff(c_6590,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6552,c_6233])).

tff(c_6821,plain,(
    ! [A_296,B_297] :
      ( r1_tarski(k2_tops_1(A_296,B_297),B_297)
      | ~ v4_pre_topc(B_297,A_296)
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6826,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_6821])).

tff(c_6833,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6172,c_6826])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6845,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6833,c_12])).

tff(c_8830,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6845])).

tff(c_7630,plain,(
    ! [A_338,B_339] :
      ( k7_subset_1(u1_struct_0(A_338),B_339,k2_tops_1(A_338,B_339)) = k1_tops_1(A_338,B_339)
      | ~ m1_subset_1(B_339,k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ l1_pre_topc(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7635,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_7630])).

tff(c_7642,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6552,c_7635])).

tff(c_7668,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7642,c_16])).

tff(c_10666,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8830,c_7668])).

tff(c_10667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6590,c_10666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.08/2.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/2.59  
% 7.38/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/2.59  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 7.38/2.59  
% 7.38/2.59  %Foreground sorts:
% 7.38/2.59  
% 7.38/2.59  
% 7.38/2.59  %Background operators:
% 7.38/2.59  
% 7.38/2.59  
% 7.38/2.59  %Foreground operators:
% 7.38/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.38/2.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.38/2.59  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.38/2.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.38/2.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.38/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.38/2.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.38/2.59  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.38/2.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.38/2.59  tff('#skF_2', type, '#skF_2': $i).
% 7.38/2.59  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.38/2.59  tff('#skF_1', type, '#skF_1': $i).
% 7.38/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.38/2.59  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.38/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.38/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.38/2.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.38/2.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.38/2.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.38/2.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.38/2.59  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.38/2.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.38/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.38/2.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.38/2.59  
% 7.38/2.62  tff(f_119, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 7.38/2.62  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.38/2.62  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.38/2.62  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 7.38/2.62  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.38/2.62  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.38/2.62  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.38/2.62  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.38/2.62  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.38/2.62  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.38/2.62  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.38/2.62  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.38/2.62  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.38/2.62  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 7.38/2.62  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 7.38/2.62  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.38/2.62  tff(c_6544, plain, (![A_276, B_277, C_278]: (k7_subset_1(A_276, B_277, C_278)=k4_xboole_0(B_277, C_278) | ~m1_subset_1(B_277, k1_zfmisc_1(A_276)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.38/2.62  tff(c_6552, plain, (![C_278]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_278)=k4_xboole_0('#skF_2', C_278))), inference(resolution, [status(thm)], [c_42, c_6544])).
% 7.38/2.62  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.38/2.62  tff(c_224, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 7.38/2.62  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.38/2.62  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.38/2.62  tff(c_1245, plain, (![B_134, A_135]: (v4_pre_topc(B_134, A_135) | k2_pre_topc(A_135, B_134)!=B_134 | ~v2_pre_topc(A_135) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.38/2.62  tff(c_1252, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1245])).
% 7.38/2.62  tff(c_1260, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_1252])).
% 7.38/2.62  tff(c_1261, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_224, c_1260])).
% 7.38/2.62  tff(c_1474, plain, (![A_142, B_143]: (k4_subset_1(u1_struct_0(A_142), B_143, k2_tops_1(A_142, B_143))=k2_pre_topc(A_142, B_143) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.38/2.62  tff(c_1479, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1474])).
% 7.38/2.62  tff(c_1486, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1479])).
% 7.38/2.62  tff(c_516, plain, (![A_87, B_88, C_89]: (k7_subset_1(A_87, B_88, C_89)=k4_xboole_0(B_88, C_89) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.38/2.62  tff(c_562, plain, (![C_92]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_92)=k4_xboole_0('#skF_2', C_92))), inference(resolution, [status(thm)], [c_42, c_516])).
% 7.38/2.62  tff(c_54, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.38/2.62  tff(c_142, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 7.38/2.62  tff(c_568, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_562, c_142])).
% 7.38/2.62  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.38/2.62  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.38/2.62  tff(c_175, plain, (![A_59, B_60]: (k2_xboole_0(A_59, B_60)=B_60 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.62  tff(c_201, plain, (![A_62, B_63]: (k2_xboole_0(k4_xboole_0(A_62, B_63), A_62)=A_62)), inference(resolution, [status(thm)], [c_14, c_175])).
% 7.38/2.62  tff(c_221, plain, (![A_1, B_63]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_63))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_201])).
% 7.38/2.62  tff(c_695, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_568, c_221])).
% 7.38/2.62  tff(c_153, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.38/2.62  tff(c_165, plain, (![A_14, B_15]: (k3_xboole_0(k4_xboole_0(A_14, B_15), A_14)=k4_xboole_0(A_14, B_15))), inference(resolution, [status(thm)], [c_14, c_153])).
% 7.38/2.62  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.38/2.62  tff(c_143, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.38/2.62  tff(c_150, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_143])).
% 7.38/2.62  tff(c_163, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_150, c_153])).
% 7.38/2.62  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.38/2.62  tff(c_297, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k3_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.38/2.62  tff(c_312, plain, (![A_71, B_72]: (r1_tarski(k3_xboole_0(A_71, B_72), A_71))), inference(superposition, [status(thm), theory('equality')], [c_297, c_14])).
% 7.38/2.62  tff(c_374, plain, (![A_77, C_78, B_79]: (r1_tarski(A_77, C_78) | ~r1_tarski(B_79, C_78) | ~r1_tarski(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.38/2.62  tff(c_791, plain, (![A_104, A_105, B_106]: (r1_tarski(A_104, A_105) | ~r1_tarski(A_104, k4_xboole_0(A_105, B_106)))), inference(resolution, [status(thm)], [c_14, c_374])).
% 7.38/2.62  tff(c_822, plain, (![A_107, B_108, B_109]: (r1_tarski(k3_xboole_0(k4_xboole_0(A_107, B_108), B_109), A_107))), inference(resolution, [status(thm)], [c_312, c_791])).
% 7.38/2.62  tff(c_966, plain, (![A_117, B_118, B_119]: (r1_tarski(k3_xboole_0(k3_xboole_0(A_117, B_118), B_119), A_117))), inference(superposition, [status(thm), theory('equality')], [c_16, c_822])).
% 7.38/2.62  tff(c_1168, plain, (![B_130, A_131, B_132]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_130, A_131), B_132), A_131))), inference(superposition, [status(thm), theory('equality')], [c_4, c_966])).
% 7.38/2.62  tff(c_1217, plain, (![B_133]: (r1_tarski(k3_xboole_0('#skF_2', B_133), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1168])).
% 7.38/2.62  tff(c_1263, plain, (![B_136]: (r1_tarski(k3_xboole_0(B_136, '#skF_2'), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1217])).
% 7.38/2.62  tff(c_1381, plain, (![B_138]: (r1_tarski(k4_xboole_0('#skF_2', B_138), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_165, c_1263])).
% 7.38/2.62  tff(c_1394, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_568, c_1381])).
% 7.38/2.62  tff(c_30, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.38/2.62  tff(c_780, plain, (![A_101, B_102, C_103]: (k4_subset_1(A_101, B_102, C_103)=k2_xboole_0(B_102, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(A_101)) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.38/2.62  tff(c_5845, plain, (![B_218, B_219, A_220]: (k4_subset_1(B_218, B_219, A_220)=k2_xboole_0(B_219, A_220) | ~m1_subset_1(B_219, k1_zfmisc_1(B_218)) | ~r1_tarski(A_220, B_218))), inference(resolution, [status(thm)], [c_30, c_780])).
% 7.38/2.62  tff(c_5858, plain, (![A_221]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_221)=k2_xboole_0('#skF_2', A_221) | ~r1_tarski(A_221, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_5845])).
% 7.38/2.62  tff(c_5876, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1394, c_5858])).
% 7.38/2.62  tff(c_5944, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1486, c_695, c_5876])).
% 7.38/2.62  tff(c_5946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1261, c_5944])).
% 7.38/2.62  tff(c_5947, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 7.38/2.62  tff(c_6171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5947, c_142])).
% 7.38/2.62  tff(c_6172, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 7.38/2.62  tff(c_6233, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6172, c_48])).
% 7.38/2.62  tff(c_6590, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6552, c_6233])).
% 7.38/2.62  tff(c_6821, plain, (![A_296, B_297]: (r1_tarski(k2_tops_1(A_296, B_297), B_297) | ~v4_pre_topc(B_297, A_296) | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0(A_296))) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.38/2.62  tff(c_6826, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_6821])).
% 7.38/2.62  tff(c_6833, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6172, c_6826])).
% 7.38/2.62  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.38/2.62  tff(c_6845, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6833, c_12])).
% 7.38/2.62  tff(c_8830, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_6845])).
% 7.38/2.62  tff(c_7630, plain, (![A_338, B_339]: (k7_subset_1(u1_struct_0(A_338), B_339, k2_tops_1(A_338, B_339))=k1_tops_1(A_338, B_339) | ~m1_subset_1(B_339, k1_zfmisc_1(u1_struct_0(A_338))) | ~l1_pre_topc(A_338))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.38/2.62  tff(c_7635, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_7630])).
% 7.38/2.62  tff(c_7642, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6552, c_7635])).
% 7.38/2.62  tff(c_7668, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7642, c_16])).
% 7.38/2.62  tff(c_10666, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8830, c_7668])).
% 7.38/2.62  tff(c_10667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6590, c_10666])).
% 7.38/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/2.62  
% 7.38/2.62  Inference rules
% 7.38/2.62  ----------------------
% 7.38/2.62  #Ref     : 0
% 7.38/2.62  #Sup     : 2596
% 7.38/2.62  #Fact    : 0
% 7.38/2.62  #Define  : 0
% 7.38/2.62  #Split   : 2
% 7.38/2.62  #Chain   : 0
% 7.38/2.62  #Close   : 0
% 7.38/2.62  
% 7.38/2.62  Ordering : KBO
% 7.38/2.62  
% 7.38/2.62  Simplification rules
% 7.38/2.62  ----------------------
% 7.38/2.62  #Subsume      : 96
% 7.38/2.62  #Demod        : 1803
% 7.38/2.62  #Tautology    : 1625
% 7.38/2.62  #SimpNegUnit  : 5
% 7.38/2.62  #BackRed      : 3
% 7.38/2.62  
% 7.38/2.62  #Partial instantiations: 0
% 7.38/2.62  #Strategies tried      : 1
% 7.38/2.62  
% 7.38/2.62  Timing (in seconds)
% 7.38/2.62  ----------------------
% 7.38/2.62  Preprocessing        : 0.35
% 7.38/2.62  Parsing              : 0.19
% 7.38/2.62  CNF conversion       : 0.02
% 7.38/2.62  Main loop            : 1.44
% 7.38/2.62  Inferencing          : 0.41
% 7.38/2.62  Reduction            : 0.65
% 7.38/2.62  Demodulation         : 0.53
% 7.38/2.62  BG Simplification    : 0.05
% 7.38/2.62  Subsumption          : 0.23
% 7.38/2.62  Abstraction          : 0.07
% 7.38/2.62  MUC search           : 0.00
% 7.38/2.62  Cooper               : 0.00
% 7.38/2.62  Total                : 1.84
% 7.38/2.62  Index Insertion      : 0.00
% 7.38/2.62  Index Deletion       : 0.00
% 7.38/2.62  Index Matching       : 0.00
% 7.38/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
