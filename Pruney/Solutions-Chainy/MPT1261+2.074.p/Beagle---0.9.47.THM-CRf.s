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
% DateTime   : Thu Dec  3 10:21:22 EST 2020

% Result     : Theorem 5.45s
% Output     : CNFRefutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 145 expanded)
%              Number of leaves         :   40 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 263 expanded)
%              Number of equality atoms :   63 (  98 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
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

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5721,plain,(
    ! [A_206,B_207,C_208] :
      ( k7_subset_1(A_206,B_207,C_208) = k4_xboole_0(B_207,C_208)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(A_206)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5724,plain,(
    ! [C_208] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_208) = k4_xboole_0('#skF_2',C_208) ),
    inference(resolution,[status(thm)],[c_38,c_5721])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_124,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1730,plain,(
    ! [B_118,A_119] :
      ( v4_pre_topc(B_118,A_119)
      | k2_pre_topc(A_119,B_118) != B_118
      | ~ v2_pre_topc(A_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1736,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1730])).

tff(c_1740,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_1736])).

tff(c_1741,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_1740])).

tff(c_2046,plain,(
    ! [A_126,B_127] :
      ( k4_subset_1(u1_struct_0(A_126),B_127,k2_tops_1(A_126,B_127)) = k2_pre_topc(A_126,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2050,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_2046])).

tff(c_2054,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2050])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_265,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_50])).

tff(c_575,plain,(
    ! [A_76,B_77,C_78] :
      ( k7_subset_1(A_76,B_77,C_78) = k4_xboole_0(B_77,C_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_628,plain,(
    ! [C_80] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_80) = k4_xboole_0('#skF_2',C_80) ),
    inference(resolution,[status(thm)],[c_38,c_575])).

tff(c_640,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_628])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_188,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_200,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_188])).

tff(c_203,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_200])).

tff(c_394,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_412,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_394])).

tff(c_415,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_412])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_197,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_188])).

tff(c_416,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_197])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_767,plain,(
    ! [A_88,B_89] : k3_xboole_0(k4_xboole_0(A_88,B_89),A_88) = k4_xboole_0(A_88,B_89) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_785,plain,(
    ! [A_88,B_89] : k5_xboole_0(k4_xboole_0(A_88,B_89),k4_xboole_0(A_88,B_89)) = k4_xboole_0(k4_xboole_0(A_88,B_89),A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_4])).

tff(c_832,plain,(
    ! [A_90,B_91] : k4_xboole_0(k4_xboole_0(A_90,B_91),A_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_785])).

tff(c_16,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_843,plain,(
    ! [A_90,B_91] : k2_xboole_0(A_90,k4_xboole_0(A_90,B_91)) = k5_xboole_0(A_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_16])).

tff(c_891,plain,(
    ! [A_92,B_93] : k2_xboole_0(A_92,k4_xboole_0(A_92,B_93)) = A_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_843])).

tff(c_907,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_891])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k2_tops_1(A_30,B_31),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1209,plain,(
    ! [A_104,B_105,C_106] :
      ( k4_subset_1(A_104,B_105,C_106) = k2_xboole_0(B_105,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5037,plain,(
    ! [A_171,B_172,B_173] :
      ( k4_subset_1(u1_struct_0(A_171),B_172,k2_tops_1(A_171,B_173)) = k2_xboole_0(B_172,k2_tops_1(A_171,B_173))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(resolution,[status(thm)],[c_32,c_1209])).

tff(c_5041,plain,(
    ! [B_173] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_173)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_173))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_5037])).

tff(c_5237,plain,(
    ! [B_176] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_176)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_176))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5041])).

tff(c_5244,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_5237])).

tff(c_5249,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2054,c_907,c_5244])).

tff(c_5251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1741,c_5249])).

tff(c_5252,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5859,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5724,c_5252])).

tff(c_5253,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6128,plain,(
    ! [A_228,B_229] :
      ( k2_pre_topc(A_228,B_229) = B_229
      | ~ v4_pre_topc(B_229,A_228)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6134,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_6128])).

tff(c_6138,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5253,c_6134])).

tff(c_7687,plain,(
    ! [A_269,B_270] :
      ( k7_subset_1(u1_struct_0(A_269),k2_pre_topc(A_269,B_270),k1_tops_1(A_269,B_270)) = k2_tops_1(A_269,B_270)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7696,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6138,c_7687])).

tff(c_7700,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_5724,c_7696])).

tff(c_7702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5859,c_7700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:16:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.45/2.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/2.11  
% 5.45/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/2.11  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.45/2.11  
% 5.45/2.11  %Foreground sorts:
% 5.45/2.11  
% 5.45/2.11  
% 5.45/2.11  %Background operators:
% 5.45/2.11  
% 5.45/2.11  
% 5.45/2.11  %Foreground operators:
% 5.45/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.45/2.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.45/2.11  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.45/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.45/2.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.45/2.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.45/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.45/2.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.45/2.11  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.45/2.11  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.45/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.45/2.11  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.45/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.45/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.45/2.11  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.45/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.45/2.11  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.45/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.45/2.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.45/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.45/2.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.45/2.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.45/2.11  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.45/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.45/2.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.45/2.11  
% 5.54/2.13  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.54/2.13  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.54/2.13  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.54/2.13  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.54/2.13  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.54/2.13  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.54/2.13  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.54/2.13  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.54/2.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.54/2.13  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.54/2.13  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.54/2.13  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.54/2.13  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.54/2.13  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.54/2.13  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.54/2.13  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.54/2.13  tff(c_5721, plain, (![A_206, B_207, C_208]: (k7_subset_1(A_206, B_207, C_208)=k4_xboole_0(B_207, C_208) | ~m1_subset_1(B_207, k1_zfmisc_1(A_206)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.54/2.13  tff(c_5724, plain, (![C_208]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_208)=k4_xboole_0('#skF_2', C_208))), inference(resolution, [status(thm)], [c_38, c_5721])).
% 5.54/2.13  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.54/2.13  tff(c_124, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 5.54/2.13  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.54/2.13  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.54/2.13  tff(c_1730, plain, (![B_118, A_119]: (v4_pre_topc(B_118, A_119) | k2_pre_topc(A_119, B_118)!=B_118 | ~v2_pre_topc(A_119) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.54/2.13  tff(c_1736, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1730])).
% 5.54/2.13  tff(c_1740, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_1736])).
% 5.54/2.13  tff(c_1741, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_124, c_1740])).
% 5.54/2.13  tff(c_2046, plain, (![A_126, B_127]: (k4_subset_1(u1_struct_0(A_126), B_127, k2_tops_1(A_126, B_127))=k2_pre_topc(A_126, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.54/2.13  tff(c_2050, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_2046])).
% 5.54/2.13  tff(c_2054, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2050])).
% 5.54/2.13  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.54/2.13  tff(c_265, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_124, c_50])).
% 5.54/2.13  tff(c_575, plain, (![A_76, B_77, C_78]: (k7_subset_1(A_76, B_77, C_78)=k4_xboole_0(B_77, C_78) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.54/2.13  tff(c_628, plain, (![C_80]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_80)=k4_xboole_0('#skF_2', C_80))), inference(resolution, [status(thm)], [c_38, c_575])).
% 5.54/2.13  tff(c_640, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_265, c_628])).
% 5.54/2.13  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.54/2.13  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.54/2.13  tff(c_188, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.54/2.13  tff(c_200, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_188])).
% 5.54/2.13  tff(c_203, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_200])).
% 5.54/2.13  tff(c_394, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.54/2.13  tff(c_412, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_394])).
% 5.54/2.13  tff(c_415, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_412])).
% 5.54/2.13  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.54/2.13  tff(c_197, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_188])).
% 5.54/2.13  tff(c_416, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_415, c_197])).
% 5.54/2.13  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.13  tff(c_125, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.54/2.13  tff(c_767, plain, (![A_88, B_89]: (k3_xboole_0(k4_xboole_0(A_88, B_89), A_88)=k4_xboole_0(A_88, B_89))), inference(resolution, [status(thm)], [c_10, c_125])).
% 5.54/2.13  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.54/2.13  tff(c_785, plain, (![A_88, B_89]: (k5_xboole_0(k4_xboole_0(A_88, B_89), k4_xboole_0(A_88, B_89))=k4_xboole_0(k4_xboole_0(A_88, B_89), A_88))), inference(superposition, [status(thm), theory('equality')], [c_767, c_4])).
% 5.54/2.13  tff(c_832, plain, (![A_90, B_91]: (k4_xboole_0(k4_xboole_0(A_90, B_91), A_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_416, c_785])).
% 5.54/2.13  tff(c_16, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.54/2.13  tff(c_843, plain, (![A_90, B_91]: (k2_xboole_0(A_90, k4_xboole_0(A_90, B_91))=k5_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_832, c_16])).
% 5.54/2.13  tff(c_891, plain, (![A_92, B_93]: (k2_xboole_0(A_92, k4_xboole_0(A_92, B_93))=A_92)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_843])).
% 5.54/2.13  tff(c_907, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_640, c_891])).
% 5.54/2.13  tff(c_32, plain, (![A_30, B_31]: (m1_subset_1(k2_tops_1(A_30, B_31), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.54/2.13  tff(c_1209, plain, (![A_104, B_105, C_106]: (k4_subset_1(A_104, B_105, C_106)=k2_xboole_0(B_105, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.54/2.13  tff(c_5037, plain, (![A_171, B_172, B_173]: (k4_subset_1(u1_struct_0(A_171), B_172, k2_tops_1(A_171, B_173))=k2_xboole_0(B_172, k2_tops_1(A_171, B_173)) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(resolution, [status(thm)], [c_32, c_1209])).
% 5.54/2.13  tff(c_5041, plain, (![B_173]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_173))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_173)) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_5037])).
% 5.54/2.13  tff(c_5237, plain, (![B_176]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_176))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_176)) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5041])).
% 5.54/2.13  tff(c_5244, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_5237])).
% 5.54/2.13  tff(c_5249, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2054, c_907, c_5244])).
% 5.54/2.13  tff(c_5251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1741, c_5249])).
% 5.54/2.13  tff(c_5252, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 5.54/2.13  tff(c_5859, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5724, c_5252])).
% 5.54/2.13  tff(c_5253, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 5.54/2.13  tff(c_6128, plain, (![A_228, B_229]: (k2_pre_topc(A_228, B_229)=B_229 | ~v4_pre_topc(B_229, A_228) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.54/2.13  tff(c_6134, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_6128])).
% 5.54/2.13  tff(c_6138, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5253, c_6134])).
% 5.54/2.13  tff(c_7687, plain, (![A_269, B_270]: (k7_subset_1(u1_struct_0(A_269), k2_pre_topc(A_269, B_270), k1_tops_1(A_269, B_270))=k2_tops_1(A_269, B_270) | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0(A_269))) | ~l1_pre_topc(A_269))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.54/2.13  tff(c_7696, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6138, c_7687])).
% 5.54/2.13  tff(c_7700, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_5724, c_7696])).
% 5.54/2.13  tff(c_7702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5859, c_7700])).
% 5.54/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.13  
% 5.54/2.13  Inference rules
% 5.54/2.13  ----------------------
% 5.54/2.13  #Ref     : 0
% 5.54/2.13  #Sup     : 1862
% 5.54/2.13  #Fact    : 0
% 5.54/2.13  #Define  : 0
% 5.54/2.13  #Split   : 2
% 5.54/2.13  #Chain   : 0
% 5.54/2.13  #Close   : 0
% 5.54/2.13  
% 5.54/2.13  Ordering : KBO
% 5.54/2.13  
% 5.54/2.13  Simplification rules
% 5.54/2.13  ----------------------
% 5.54/2.13  #Subsume      : 82
% 5.54/2.13  #Demod        : 2548
% 5.54/2.13  #Tautology    : 1573
% 5.54/2.13  #SimpNegUnit  : 4
% 5.54/2.13  #BackRed      : 3
% 5.54/2.13  
% 5.54/2.13  #Partial instantiations: 0
% 5.54/2.13  #Strategies tried      : 1
% 5.54/2.13  
% 5.54/2.13  Timing (in seconds)
% 5.54/2.13  ----------------------
% 5.54/2.13  Preprocessing        : 0.34
% 5.54/2.13  Parsing              : 0.18
% 5.54/2.13  CNF conversion       : 0.02
% 5.54/2.13  Main loop            : 1.01
% 5.54/2.13  Inferencing          : 0.30
% 5.54/2.13  Reduction            : 0.51
% 5.54/2.13  Demodulation         : 0.43
% 5.54/2.13  BG Simplification    : 0.03
% 5.54/2.13  Subsumption          : 0.12
% 5.54/2.13  Abstraction          : 0.05
% 5.54/2.13  MUC search           : 0.00
% 5.54/2.13  Cooper               : 0.00
% 5.54/2.13  Total                : 1.38
% 5.54/2.13  Index Insertion      : 0.00
% 5.54/2.13  Index Deletion       : 0.00
% 5.54/2.13  Index Matching       : 0.00
% 5.54/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
