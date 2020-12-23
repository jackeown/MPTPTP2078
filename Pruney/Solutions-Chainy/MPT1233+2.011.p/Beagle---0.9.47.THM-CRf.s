%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:31 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 297 expanded)
%              Number of leaves         :   51 ( 122 expanded)
%              Depth                    :   15
%              Number of atoms          :  125 ( 427 expanded)
%              Number of equality atoms :   45 ( 180 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_129,axiom,(
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

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_66,plain,(
    k1_tops_1('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    ! [A_43] : k2_subset_1(A_43) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_46] : m1_subset_1(k2_subset_1(A_46),k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_71,plain,(
    ! [A_46] : m1_subset_1(A_46,k1_zfmisc_1(A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_18,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_196,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_205,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_196])).

tff(c_208,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_205])).

tff(c_42,plain,(
    ! [A_49] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_502,plain,(
    ! [A_145,B_146] :
      ( k4_xboole_0(A_145,B_146) = k3_subset_1(A_145,B_146)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_516,plain,(
    ! [A_49] : k4_xboole_0(A_49,k1_xboole_0) = k3_subset_1(A_49,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_502])).

tff(c_524,plain,(
    ! [A_49] : k3_subset_1(A_49,k1_xboole_0) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_516])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_527,plain,(
    ! [A_147] : k3_subset_1(A_147,k1_xboole_0) = A_147 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_516])).

tff(c_54,plain,(
    ! [A_60] :
      ( l1_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_56,plain,(
    ! [A_61] :
      ( v1_xboole_0(k1_struct_0(A_61))
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_107,plain,(
    ! [B_79,A_80] :
      ( ~ v1_xboole_0(B_79)
      | B_79 = A_80
      | ~ v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_114,plain,(
    ! [A_81] :
      ( k1_xboole_0 = A_81
      | ~ v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_12,c_107])).

tff(c_133,plain,(
    ! [A_84] :
      ( k1_struct_0(A_84) = k1_xboole_0
      | ~ l1_struct_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_56,c_114])).

tff(c_138,plain,(
    ! [A_85] :
      ( k1_struct_0(A_85) = k1_xboole_0
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_54,c_133])).

tff(c_142,plain,(
    k1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_138])).

tff(c_209,plain,(
    ! [A_104] :
      ( k3_subset_1(u1_struct_0(A_104),k1_struct_0(A_104)) = k2_struct_0(A_104)
      | ~ l1_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_218,plain,
    ( k3_subset_1(u1_struct_0('#skF_3'),k1_xboole_0) = k2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_209])).

tff(c_243,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_253,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_243])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_253])).

tff(c_258,plain,(
    k3_subset_1(u1_struct_0('#skF_3'),k1_xboole_0) = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_540,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_258])).

tff(c_803,plain,(
    ! [B_176,A_177] :
      ( v4_pre_topc(B_176,A_177)
      | ~ v1_xboole_0(B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_814,plain,(
    ! [B_176] :
      ( v4_pre_topc(B_176,'#skF_3')
      | ~ v1_xboole_0(B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_803])).

tff(c_982,plain,(
    ! [B_186] :
      ( v4_pre_topc(B_186,'#skF_3')
      | ~ v1_xboole_0(B_186)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_814])).

tff(c_1006,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_982])).

tff(c_1018,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1006])).

tff(c_1020,plain,(
    ! [A_187,B_188] :
      ( k2_pre_topc(A_187,B_188) = B_188
      | ~ v4_pre_topc(B_188,A_187)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1031,plain,(
    ! [B_188] :
      ( k2_pre_topc('#skF_3',B_188) = B_188
      | ~ v4_pre_topc(B_188,'#skF_3')
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_1020])).

tff(c_1062,plain,(
    ! [B_189] :
      ( k2_pre_topc('#skF_3',B_189) = B_189
      | ~ v4_pre_topc(B_189,'#skF_3')
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1031])).

tff(c_1086,plain,
    ( k2_pre_topc('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1062])).

tff(c_1098,plain,(
    k2_pre_topc('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_1086])).

tff(c_315,plain,(
    ! [A_125,B_126] :
      ( k3_subset_1(A_125,k3_subset_1(A_125,B_126)) = B_126
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_323,plain,(
    ! [A_49] : k3_subset_1(A_49,k3_subset_1(A_49,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_315])).

tff(c_526,plain,(
    ! [A_49] : k3_subset_1(A_49,A_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_323])).

tff(c_1827,plain,(
    ! [A_250,B_251] :
      ( k3_subset_1(u1_struct_0(A_250),k2_pre_topc(A_250,k3_subset_1(u1_struct_0(A_250),B_251))) = k1_tops_1(A_250,B_251)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ l1_pre_topc(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1848,plain,(
    ! [B_251] :
      ( k3_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3',k3_subset_1(k2_struct_0('#skF_3'),B_251))) = k1_tops_1('#skF_3',B_251)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_1827])).

tff(c_1955,plain,(
    ! [B_259] :
      ( k3_subset_1(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',k3_subset_1(k2_struct_0('#skF_3'),B_259))) = k1_tops_1('#skF_3',B_259)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_540,c_540,c_1848])).

tff(c_1974,plain,
    ( k3_subset_1(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',k1_xboole_0)) = k1_tops_1('#skF_3',k2_struct_0('#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_1955])).

tff(c_1986,plain,(
    k1_tops_1('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_524,c_1098,c_1974])).

tff(c_1988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:37:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.65  
% 3.87/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.65  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 3.87/1.65  
% 3.87/1.65  %Foreground sorts:
% 3.87/1.65  
% 3.87/1.65  
% 3.87/1.65  %Background operators:
% 3.87/1.65  
% 3.87/1.65  
% 3.87/1.65  %Foreground operators:
% 3.87/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.87/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.87/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.87/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.87/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.87/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.87/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.87/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.87/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.87/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.87/1.65  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.87/1.65  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.87/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.87/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.87/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.87/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.87/1.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.87/1.65  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.87/1.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.87/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.87/1.65  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 3.87/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.87/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.87/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.87/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.87/1.65  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.87/1.65  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.87/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.87/1.65  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.87/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.87/1.65  
% 4.08/1.67  tff(f_143, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 4.08/1.67  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.08/1.67  tff(f_73, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.08/1.67  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.08/1.67  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.08/1.67  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.08/1.67  tff(f_79, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.08/1.67  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.08/1.67  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.08/1.67  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.08/1.67  tff(f_110, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 4.08/1.67  tff(f_53, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.08/1.67  tff(f_114, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 4.08/1.67  tff(f_102, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 4.08/1.67  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.08/1.67  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.08/1.67  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 4.08/1.67  tff(c_66, plain, (k1_tops_1('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.67  tff(c_34, plain, (![A_43]: (k2_subset_1(A_43)=A_43)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.08/1.67  tff(c_38, plain, (![A_46]: (m1_subset_1(k2_subset_1(A_46), k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.08/1.67  tff(c_71, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1(A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 4.08/1.67  tff(c_18, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.08/1.67  tff(c_16, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.08/1.67  tff(c_196, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.08/1.67  tff(c_205, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_196])).
% 4.08/1.67  tff(c_208, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_205])).
% 4.08/1.67  tff(c_42, plain, (![A_49]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.08/1.67  tff(c_502, plain, (![A_145, B_146]: (k4_xboole_0(A_145, B_146)=k3_subset_1(A_145, B_146) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.08/1.67  tff(c_516, plain, (![A_49]: (k4_xboole_0(A_49, k1_xboole_0)=k3_subset_1(A_49, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_502])).
% 4.08/1.67  tff(c_524, plain, (![A_49]: (k3_subset_1(A_49, k1_xboole_0)=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_208, c_516])).
% 4.08/1.67  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.08/1.67  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.67  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.67  tff(c_527, plain, (![A_147]: (k3_subset_1(A_147, k1_xboole_0)=A_147)), inference(demodulation, [status(thm), theory('equality')], [c_208, c_516])).
% 4.08/1.67  tff(c_54, plain, (![A_60]: (l1_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.08/1.67  tff(c_56, plain, (![A_61]: (v1_xboole_0(k1_struct_0(A_61)) | ~l1_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.08/1.67  tff(c_107, plain, (![B_79, A_80]: (~v1_xboole_0(B_79) | B_79=A_80 | ~v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.67  tff(c_114, plain, (![A_81]: (k1_xboole_0=A_81 | ~v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_12, c_107])).
% 4.08/1.67  tff(c_133, plain, (![A_84]: (k1_struct_0(A_84)=k1_xboole_0 | ~l1_struct_0(A_84))), inference(resolution, [status(thm)], [c_56, c_114])).
% 4.08/1.67  tff(c_138, plain, (![A_85]: (k1_struct_0(A_85)=k1_xboole_0 | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_54, c_133])).
% 4.08/1.67  tff(c_142, plain, (k1_struct_0('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_138])).
% 4.08/1.67  tff(c_209, plain, (![A_104]: (k3_subset_1(u1_struct_0(A_104), k1_struct_0(A_104))=k2_struct_0(A_104) | ~l1_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.08/1.67  tff(c_218, plain, (k3_subset_1(u1_struct_0('#skF_3'), k1_xboole_0)=k2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_209])).
% 4.08/1.67  tff(c_243, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_218])).
% 4.08/1.67  tff(c_253, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_243])).
% 4.08/1.67  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_253])).
% 4.08/1.67  tff(c_258, plain, (k3_subset_1(u1_struct_0('#skF_3'), k1_xboole_0)=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_218])).
% 4.08/1.67  tff(c_540, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_527, c_258])).
% 4.08/1.67  tff(c_803, plain, (![B_176, A_177]: (v4_pre_topc(B_176, A_177) | ~v1_xboole_0(B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.08/1.67  tff(c_814, plain, (![B_176]: (v4_pre_topc(B_176, '#skF_3') | ~v1_xboole_0(B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_540, c_803])).
% 4.08/1.67  tff(c_982, plain, (![B_186]: (v4_pre_topc(B_186, '#skF_3') | ~v1_xboole_0(B_186) | ~m1_subset_1(B_186, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_814])).
% 4.08/1.67  tff(c_1006, plain, (v4_pre_topc(k1_xboole_0, '#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_982])).
% 4.08/1.67  tff(c_1018, plain, (v4_pre_topc(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1006])).
% 4.08/1.67  tff(c_1020, plain, (![A_187, B_188]: (k2_pre_topc(A_187, B_188)=B_188 | ~v4_pre_topc(B_188, A_187) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.08/1.67  tff(c_1031, plain, (![B_188]: (k2_pre_topc('#skF_3', B_188)=B_188 | ~v4_pre_topc(B_188, '#skF_3') | ~m1_subset_1(B_188, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_540, c_1020])).
% 4.08/1.67  tff(c_1062, plain, (![B_189]: (k2_pre_topc('#skF_3', B_189)=B_189 | ~v4_pre_topc(B_189, '#skF_3') | ~m1_subset_1(B_189, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1031])).
% 4.08/1.67  tff(c_1086, plain, (k2_pre_topc('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_42, c_1062])).
% 4.08/1.67  tff(c_1098, plain, (k2_pre_topc('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_1086])).
% 4.08/1.67  tff(c_315, plain, (![A_125, B_126]: (k3_subset_1(A_125, k3_subset_1(A_125, B_126))=B_126 | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.08/1.67  tff(c_323, plain, (![A_49]: (k3_subset_1(A_49, k3_subset_1(A_49, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_315])).
% 4.08/1.67  tff(c_526, plain, (![A_49]: (k3_subset_1(A_49, A_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_524, c_323])).
% 4.08/1.67  tff(c_1827, plain, (![A_250, B_251]: (k3_subset_1(u1_struct_0(A_250), k2_pre_topc(A_250, k3_subset_1(u1_struct_0(A_250), B_251)))=k1_tops_1(A_250, B_251) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_250))) | ~l1_pre_topc(A_250))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.08/1.67  tff(c_1848, plain, (![B_251]: (k3_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', k3_subset_1(k2_struct_0('#skF_3'), B_251)))=k1_tops_1('#skF_3', B_251) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_540, c_1827])).
% 4.08/1.67  tff(c_1955, plain, (![B_259]: (k3_subset_1(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', k3_subset_1(k2_struct_0('#skF_3'), B_259)))=k1_tops_1('#skF_3', B_259) | ~m1_subset_1(B_259, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_540, c_540, c_1848])).
% 4.08/1.67  tff(c_1974, plain, (k3_subset_1(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', k1_xboole_0))=k1_tops_1('#skF_3', k2_struct_0('#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_526, c_1955])).
% 4.08/1.67  tff(c_1986, plain, (k1_tops_1('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_524, c_1098, c_1974])).
% 4.08/1.67  tff(c_1988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1986])).
% 4.08/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.67  
% 4.08/1.67  Inference rules
% 4.08/1.67  ----------------------
% 4.08/1.67  #Ref     : 0
% 4.08/1.67  #Sup     : 423
% 4.08/1.67  #Fact    : 0
% 4.08/1.67  #Define  : 0
% 4.08/1.67  #Split   : 4
% 4.08/1.67  #Chain   : 0
% 4.08/1.67  #Close   : 0
% 4.08/1.67  
% 4.08/1.67  Ordering : KBO
% 4.08/1.67  
% 4.08/1.67  Simplification rules
% 4.08/1.67  ----------------------
% 4.08/1.67  #Subsume      : 59
% 4.08/1.67  #Demod        : 119
% 4.08/1.67  #Tautology    : 127
% 4.08/1.67  #SimpNegUnit  : 19
% 4.08/1.67  #BackRed      : 14
% 4.08/1.67  
% 4.08/1.67  #Partial instantiations: 0
% 4.08/1.67  #Strategies tried      : 1
% 4.08/1.67  
% 4.08/1.67  Timing (in seconds)
% 4.08/1.67  ----------------------
% 4.08/1.67  Preprocessing        : 0.35
% 4.08/1.67  Parsing              : 0.19
% 4.08/1.67  CNF conversion       : 0.03
% 4.08/1.67  Main loop            : 0.56
% 4.08/1.67  Inferencing          : 0.20
% 4.08/1.67  Reduction            : 0.16
% 4.08/1.67  Demodulation         : 0.11
% 4.08/1.67  BG Simplification    : 0.03
% 4.08/1.67  Subsumption          : 0.12
% 4.08/1.67  Abstraction          : 0.03
% 4.08/1.67  MUC search           : 0.00
% 4.08/1.67  Cooper               : 0.00
% 4.08/1.67  Total                : 0.94
% 4.08/1.67  Index Insertion      : 0.00
% 4.08/1.67  Index Deletion       : 0.00
% 4.08/1.67  Index Matching       : 0.00
% 4.08/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
