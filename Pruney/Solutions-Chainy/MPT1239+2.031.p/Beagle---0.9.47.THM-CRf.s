%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:45 EST 2020

% Result     : Theorem 34.68s
% Output     : CNFRefutation 34.82s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 248 expanded)
%              Number of leaves         :   29 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          :  188 ( 524 expanded)
%              Number of equality atoms :    8 (  25 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k1_tops_1(A,k7_subset_1(u1_struct_0(A),B,C)),k7_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_70,plain,(
    ! [A_69,B_70,C_71] :
      ( k7_subset_1(A_69,B_70,C_71) = k4_xboole_0(B_70,C_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,(
    ! [C_74] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_74) = k4_xboole_0('#skF_2',C_74) ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_16,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k7_subset_1(A_22,B_23,C_24),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_102,plain,(
    ! [C_74] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_74),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_16])).

tff(c_108,plain,(
    ! [C_74] : m1_subset_1(k4_xboole_0('#skF_2',C_74),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_102])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_33,B_37,C_39] :
      ( r1_tarski(k1_tops_1(A_33,B_37),k1_tops_1(A_33,C_39))
      | ~ r1_tarski(B_37,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [A_19,B_20,C_21] :
      ( r1_tarski(A_19,k4_xboole_0(B_20,C_21))
      | ~ r1_xboole_0(A_19,C_21)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_254,plain,(
    ! [A_110,B_111] :
      ( m1_subset_1(k1_tops_1(A_110,B_111),k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [A_25,B_26,C_27] :
      ( k7_subset_1(A_25,B_26,C_27) = k4_xboole_0(B_26,C_27)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1073,plain,(
    ! [A_285,B_286,C_287] :
      ( k7_subset_1(u1_struct_0(A_285),k1_tops_1(A_285,B_286),C_287) = k4_xboole_0(k1_tops_1(A_285,B_286),C_287)
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ l1_pre_topc(A_285) ) ),
    inference(resolution,[status(thm)],[c_254,c_18])).

tff(c_1088,plain,(
    ! [C_287] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_287) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_287)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1073])).

tff(c_1107,plain,(
    ! [C_287] : k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_287) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1088])).

tff(c_78,plain,(
    ! [C_71] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_71) = k4_xboole_0('#skF_2',C_71) ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_26,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_95,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_26])).

tff(c_1111,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_95])).

tff(c_1139,plain,
    ( ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_1111])).

tff(c_4412,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1139])).

tff(c_4415,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_4412])).

tff(c_4419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_108,c_30,c_2,c_4415])).

tff(c_4420,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1139])).

tff(c_124,plain,(
    ! [C_76] : m1_subset_1(k4_xboole_0('#skF_2',C_76),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_102])).

tff(c_22,plain,(
    ! [A_30,B_32] :
      ( r1_tarski(k1_tops_1(A_30,B_32),B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_126,plain,(
    ! [C_76] :
      ( r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_76)),k4_xboole_0('#skF_2',C_76))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_124,c_22])).

tff(c_131,plain,(
    ! [C_76] : r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_76)),k4_xboole_0('#skF_2',C_76)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_126])).

tff(c_42,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_tarski(A_55,k2_xboole_0(B_56,C_57))
      | ~ r1_tarski(k4_xboole_0(A_55,B_56),C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(resolution,[status(thm)],[c_2,c_42])).

tff(c_51,plain,(
    ! [A_58,B_59] : r1_tarski(A_58,k2_xboole_0(B_59,A_58)) ),
    inference(resolution,[status(thm)],[c_2,c_42])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,k2_xboole_0(B_7,C_8))
      | ~ r1_tarski(k4_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_6,B_7,B_59] : r1_tarski(A_6,k2_xboole_0(B_7,k2_xboole_0(B_59,k4_xboole_0(A_6,B_7)))) ),
    inference(resolution,[status(thm)],[c_51,c_6])).

tff(c_12,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_xboole_0(A_16,k4_xboole_0(C_18,B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_172,plain,(
    ! [A_84,C_85,B_86,D_87] :
      ( r1_xboole_0(A_84,C_85)
      | ~ r1_xboole_0(B_86,D_87)
      | ~ r1_tarski(C_85,D_87)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_392,plain,(
    ! [C_165,C_161,B_163,A_164,A_162] :
      ( r1_xboole_0(A_162,C_161)
      | ~ r1_tarski(C_161,k4_xboole_0(C_165,B_163))
      | ~ r1_tarski(A_162,A_164)
      | ~ r1_tarski(A_164,B_163) ) ),
    inference(resolution,[status(thm)],[c_12,c_172])).

tff(c_416,plain,(
    ! [B_166,A_167,A_169,C_168,B_170] :
      ( r1_xboole_0(A_169,k4_xboole_0(k4_xboole_0(C_168,B_166),B_170))
      | ~ r1_tarski(A_169,A_167)
      | ~ r1_tarski(A_167,B_166) ) ),
    inference(resolution,[status(thm)],[c_2,c_392])).

tff(c_4914,plain,(
    ! [A_806,B_801,B_805,B_802,B_803,C_804] :
      ( r1_xboole_0(A_806,k4_xboole_0(k4_xboole_0(C_804,B_802),B_803))
      | ~ r1_tarski(k2_xboole_0(B_805,k2_xboole_0(B_801,k4_xboole_0(A_806,B_805))),B_802) ) ),
    inference(resolution,[status(thm)],[c_56,c_416])).

tff(c_4938,plain,(
    ! [A_806,B_801,B_2,B_805,B_803,C_804] : r1_xboole_0(A_806,k4_xboole_0(k4_xboole_0(C_804,k2_xboole_0(B_2,k2_xboole_0(B_805,k2_xboole_0(B_801,k4_xboole_0(A_806,B_805))))),B_803)) ),
    inference(resolution,[status(thm)],[c_50,c_4914])).

tff(c_8142,plain,(
    ! [C_1047,B_1044,C_1042,A_1046,B_1045,B_1043] :
      ( r1_xboole_0(A_1046,k4_xboole_0(k4_xboole_0(C_1047,B_1043),B_1044))
      | ~ r1_tarski(k4_xboole_0(B_1045,C_1042),B_1043)
      | ~ r1_xboole_0(A_1046,C_1042)
      | ~ r1_tarski(A_1046,B_1045) ) ),
    inference(resolution,[status(thm)],[c_14,c_416])).

tff(c_8227,plain,(
    ! [C_1062,B_1064,A_1065,A_1066,B_1063] :
      ( r1_xboole_0(A_1066,k4_xboole_0(k4_xboole_0(C_1062,A_1065),B_1063))
      | ~ r1_xboole_0(A_1066,B_1064)
      | ~ r1_tarski(A_1066,A_1065) ) ),
    inference(resolution,[status(thm)],[c_2,c_8142])).

tff(c_8687,plain,(
    ! [A_1067,C_1068,A_1069,B_1070] :
      ( r1_xboole_0(A_1067,k4_xboole_0(k4_xboole_0(C_1068,A_1069),B_1070))
      | ~ r1_tarski(A_1067,A_1069) ) ),
    inference(resolution,[status(thm)],[c_4938,c_8227])).

tff(c_10,plain,(
    ! [A_12,C_14,B_13,D_15] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_xboole_0(B_13,D_15)
      | ~ r1_tarski(C_14,D_15)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_25494,plain,(
    ! [A_2354,C_2352,A_2355,A_2351,C_2353,B_2350] :
      ( r1_xboole_0(A_2351,C_2352)
      | ~ r1_tarski(C_2352,k4_xboole_0(k4_xboole_0(C_2353,A_2354),B_2350))
      | ~ r1_tarski(A_2351,A_2355)
      | ~ r1_tarski(A_2355,A_2354) ) ),
    inference(resolution,[status(thm)],[c_8687,c_10])).

tff(c_26309,plain,(
    ! [A_2410,A_2415,C_2414,B_2412,B_2413,A_2411] :
      ( r1_xboole_0(A_2415,k4_xboole_0(k4_xboole_0(k4_xboole_0(C_2414,A_2411),B_2412),B_2413))
      | ~ r1_tarski(A_2415,A_2410)
      | ~ r1_tarski(A_2410,A_2411) ) ),
    inference(resolution,[status(thm)],[c_2,c_25494])).

tff(c_26435,plain,(
    ! [A_2426,C_2424,B_2427,B_2425,B_2428,A_2429] :
      ( r1_xboole_0(A_2429,k4_xboole_0(k4_xboole_0(k4_xboole_0(C_2424,A_2426),B_2427),B_2425))
      | ~ r1_tarski(k2_xboole_0(B_2428,A_2429),A_2426) ) ),
    inference(resolution,[status(thm)],[c_50,c_26309])).

tff(c_26463,plain,(
    ! [B_2,C_2424,B_2427,B_2425,B_2428,A_2429] : r1_xboole_0(A_2429,k4_xboole_0(k4_xboole_0(k4_xboole_0(C_2424,k2_xboole_0(B_2,k2_xboole_0(B_2428,A_2429))),B_2427),B_2425)) ),
    inference(resolution,[status(thm)],[c_50,c_26435])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_80,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k1_tops_1(A_72,B_73),B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_87,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_80])).

tff(c_94,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87])).

tff(c_508,plain,(
    ! [A_194,C_195,A_196] :
      ( r1_xboole_0(A_194,k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_195)))
      | ~ r1_tarski(A_194,A_196)
      | ~ r1_tarski(A_196,C_195) ) ),
    inference(resolution,[status(thm)],[c_131,c_392])).

tff(c_22407,plain,(
    ! [A_2025,C_2026,B_2027,B_2028] :
      ( r1_xboole_0(A_2025,k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_2026)))
      | ~ r1_tarski(k2_xboole_0(B_2027,k2_xboole_0(B_2028,k4_xboole_0(A_2025,B_2027))),C_2026) ) ),
    inference(resolution,[status(thm)],[c_56,c_508])).

tff(c_22442,plain,(
    ! [A_2025,B_2,B_2027,B_2028] : r1_xboole_0(A_2025,k1_tops_1('#skF_1',k4_xboole_0('#skF_2',k2_xboole_0(B_2,k2_xboole_0(B_2027,k2_xboole_0(B_2028,k4_xboole_0(A_2025,B_2027))))))) ),
    inference(resolution,[status(thm)],[c_50,c_22407])).

tff(c_57,plain,(
    ! [A_60,B_61,B_62] : r1_tarski(A_60,k2_xboole_0(B_61,k2_xboole_0(B_62,k4_xboole_0(A_60,B_61)))) ),
    inference(resolution,[status(thm)],[c_51,c_6])).

tff(c_62,plain,(
    ! [A_6,B_7,B_61,B_62] : r1_tarski(A_6,k2_xboole_0(B_7,k2_xboole_0(B_61,k2_xboole_0(B_62,k4_xboole_0(k4_xboole_0(A_6,B_7),B_61))))) ),
    inference(resolution,[status(thm)],[c_57,c_6])).

tff(c_817,plain,(
    ! [A_268,A_267,C_264,B_266,A_265] :
      ( r1_xboole_0(A_268,A_267)
      | ~ r1_tarski(A_268,A_265)
      | ~ r1_tarski(A_265,C_264)
      | ~ r1_xboole_0(A_267,C_264)
      | ~ r1_tarski(A_267,B_266) ) ),
    inference(resolution,[status(thm)],[c_14,c_392])).

tff(c_1301,plain,(
    ! [B_296,B_297,A_299,A_298,C_295] :
      ( r1_xboole_0(k4_xboole_0(A_299,B_297),A_298)
      | ~ r1_tarski(A_299,C_295)
      | ~ r1_xboole_0(A_298,C_295)
      | ~ r1_tarski(A_298,B_296) ) ),
    inference(resolution,[status(thm)],[c_2,c_817])).

tff(c_1564,plain,(
    ! [B_322,A_320,B_321,B_324,A_323] :
      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(A_323,B_322),B_321),A_320)
      | ~ r1_xboole_0(A_320,A_323)
      | ~ r1_tarski(A_320,B_324) ) ),
    inference(resolution,[status(thm)],[c_2,c_1301])).

tff(c_1619,plain,(
    ! [A_325,B_326,B_327,A_328] :
      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(A_325,B_326),B_327),A_328)
      | ~ r1_xboole_0(A_328,A_325) ) ),
    inference(resolution,[status(thm)],[c_62,c_1564])).

tff(c_8,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_xboole_0(A_9,C_11)
      | ~ r1_xboole_0(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1687,plain,(
    ! [B_341,A_339,B_342,A_338,A_340] :
      ( r1_xboole_0(A_340,A_339)
      | ~ r1_tarski(A_340,k4_xboole_0(k4_xboole_0(A_338,B_341),B_342))
      | ~ r1_xboole_0(A_339,A_338) ) ),
    inference(resolution,[status(thm)],[c_1619,c_8])).

tff(c_2844,plain,(
    ! [A_528,B_526,C_525,A_527,A_529] :
      ( r1_xboole_0(A_527,A_529)
      | ~ r1_xboole_0(A_529,A_528)
      | ~ r1_xboole_0(A_527,C_525)
      | ~ r1_tarski(A_527,k4_xboole_0(A_528,B_526)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1687])).

tff(c_44590,plain,(
    ! [C_3068,B_3066,A_3071,C_3070,A_3069,B_3067] :
      ( r1_xboole_0(A_3071,A_3069)
      | ~ r1_xboole_0(A_3071,C_3068)
      | ~ r1_tarski(A_3071,k4_xboole_0(k4_xboole_0(C_3070,B_3067),B_3066))
      | ~ r1_tarski(A_3069,B_3067) ) ),
    inference(resolution,[status(thm)],[c_12,c_2844])).

tff(c_45809,plain,(
    ! [A_3075,B_3073,B_3074,A_3076,C_3072] :
      ( r1_xboole_0(A_3076,A_3075)
      | ~ r1_tarski(A_3076,k4_xboole_0(k4_xboole_0(C_3072,B_3073),B_3074))
      | ~ r1_tarski(A_3075,B_3073) ) ),
    inference(resolution,[status(thm)],[c_22442,c_44590])).

tff(c_46813,plain,(
    ! [B_3124,C_3127,A_3126,C_3123,A_3125] :
      ( r1_xboole_0(A_3125,A_3126)
      | ~ r1_tarski(A_3126,B_3124)
      | ~ r1_xboole_0(A_3125,C_3123)
      | ~ r1_tarski(A_3125,k4_xboole_0(C_3127,B_3124)) ) ),
    inference(resolution,[status(thm)],[c_14,c_45809])).

tff(c_46919,plain,(
    ! [A_3128,C_3129,C_3130] :
      ( r1_xboole_0(A_3128,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_xboole_0(A_3128,C_3129)
      | ~ r1_tarski(A_3128,k4_xboole_0(C_3130,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_94,c_46813])).

tff(c_48173,plain,(
    ! [A_3131,C_3132] :
      ( r1_xboole_0(A_3131,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_3131,k4_xboole_0(C_3132,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_26463,c_46919])).

tff(c_48215,plain,(
    r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_131,c_48173])).

tff(c_48241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4420,c_48215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.68/25.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.68/25.18  
% 34.68/25.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.68/25.18  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 34.68/25.18  
% 34.68/25.18  %Foreground sorts:
% 34.68/25.18  
% 34.68/25.18  
% 34.68/25.18  %Background operators:
% 34.68/25.18  
% 34.68/25.18  
% 34.68/25.18  %Foreground operators:
% 34.68/25.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.68/25.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 34.68/25.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 34.68/25.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 34.68/25.18  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 34.68/25.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 34.68/25.18  tff('#skF_2', type, '#skF_2': $i).
% 34.68/25.18  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 34.68/25.18  tff('#skF_3', type, '#skF_3': $i).
% 34.68/25.18  tff('#skF_1', type, '#skF_1': $i).
% 34.68/25.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 34.68/25.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.68/25.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.68/25.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 34.68/25.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 34.68/25.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 34.68/25.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 34.68/25.18  
% 34.82/25.20  tff(f_105, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, k7_subset_1(u1_struct_0(A), B, C)), k7_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 34.82/25.20  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 34.82/25.20  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 34.82/25.20  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 34.82/25.20  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 34.82/25.20  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 34.82/25.20  tff(f_73, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 34.82/25.20  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 34.82/25.20  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 34.82/25.20  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 34.82/25.20  tff(f_49, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 34.82/25.20  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 34.82/25.20  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 34.82/25.20  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 34.82/25.20  tff(c_70, plain, (![A_69, B_70, C_71]: (k7_subset_1(A_69, B_70, C_71)=k4_xboole_0(B_70, C_71) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 34.82/25.20  tff(c_96, plain, (![C_74]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_74)=k4_xboole_0('#skF_2', C_74))), inference(resolution, [status(thm)], [c_30, c_70])).
% 34.82/25.20  tff(c_16, plain, (![A_22, B_23, C_24]: (m1_subset_1(k7_subset_1(A_22, B_23, C_24), k1_zfmisc_1(A_22)) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 34.82/25.20  tff(c_102, plain, (![C_74]: (m1_subset_1(k4_xboole_0('#skF_2', C_74), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_96, c_16])).
% 34.82/25.20  tff(c_108, plain, (![C_74]: (m1_subset_1(k4_xboole_0('#skF_2', C_74), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_102])).
% 34.82/25.20  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 34.82/25.20  tff(c_24, plain, (![A_33, B_37, C_39]: (r1_tarski(k1_tops_1(A_33, B_37), k1_tops_1(A_33, C_39)) | ~r1_tarski(B_37, C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_92])).
% 34.82/25.20  tff(c_14, plain, (![A_19, B_20, C_21]: (r1_tarski(A_19, k4_xboole_0(B_20, C_21)) | ~r1_xboole_0(A_19, C_21) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 34.82/25.20  tff(c_254, plain, (![A_110, B_111]: (m1_subset_1(k1_tops_1(A_110, B_111), k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_73])).
% 34.82/25.20  tff(c_18, plain, (![A_25, B_26, C_27]: (k7_subset_1(A_25, B_26, C_27)=k4_xboole_0(B_26, C_27) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 34.82/25.20  tff(c_1073, plain, (![A_285, B_286, C_287]: (k7_subset_1(u1_struct_0(A_285), k1_tops_1(A_285, B_286), C_287)=k4_xboole_0(k1_tops_1(A_285, B_286), C_287) | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0(A_285))) | ~l1_pre_topc(A_285))), inference(resolution, [status(thm)], [c_254, c_18])).
% 34.82/25.20  tff(c_1088, plain, (![C_287]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_287)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_287) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1073])).
% 34.82/25.20  tff(c_1107, plain, (![C_287]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_287)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_287))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1088])).
% 34.82/25.20  tff(c_78, plain, (![C_71]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_71)=k4_xboole_0('#skF_2', C_71))), inference(resolution, [status(thm)], [c_30, c_70])).
% 34.82/25.20  tff(c_26, plain, (~r1_tarski(k1_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 34.82/25.20  tff(c_95, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_26])).
% 34.82/25.20  tff(c_1111, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_95])).
% 34.82/25.20  tff(c_1139, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_1111])).
% 34.82/25.20  tff(c_4412, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1139])).
% 34.82/25.20  tff(c_4415, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_4412])).
% 34.82/25.20  tff(c_4419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_108, c_30, c_2, c_4415])).
% 34.82/25.20  tff(c_4420, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_1139])).
% 34.82/25.20  tff(c_124, plain, (![C_76]: (m1_subset_1(k4_xboole_0('#skF_2', C_76), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_102])).
% 34.82/25.20  tff(c_22, plain, (![A_30, B_32]: (r1_tarski(k1_tops_1(A_30, B_32), B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_80])).
% 34.82/25.20  tff(c_126, plain, (![C_76]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_76)), k4_xboole_0('#skF_2', C_76)) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_124, c_22])).
% 34.82/25.20  tff(c_131, plain, (![C_76]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_76)), k4_xboole_0('#skF_2', C_76)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_126])).
% 34.82/25.20  tff(c_42, plain, (![A_55, B_56, C_57]: (r1_tarski(A_55, k2_xboole_0(B_56, C_57)) | ~r1_tarski(k4_xboole_0(A_55, B_56), C_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 34.82/25.20  tff(c_50, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(resolution, [status(thm)], [c_2, c_42])).
% 34.82/25.20  tff(c_51, plain, (![A_58, B_59]: (r1_tarski(A_58, k2_xboole_0(B_59, A_58)))), inference(resolution, [status(thm)], [c_2, c_42])).
% 34.82/25.20  tff(c_6, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, k2_xboole_0(B_7, C_8)) | ~r1_tarski(k4_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 34.82/25.20  tff(c_56, plain, (![A_6, B_7, B_59]: (r1_tarski(A_6, k2_xboole_0(B_7, k2_xboole_0(B_59, k4_xboole_0(A_6, B_7)))))), inference(resolution, [status(thm)], [c_51, c_6])).
% 34.82/25.20  tff(c_12, plain, (![A_16, C_18, B_17]: (r1_xboole_0(A_16, k4_xboole_0(C_18, B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 34.82/25.20  tff(c_172, plain, (![A_84, C_85, B_86, D_87]: (r1_xboole_0(A_84, C_85) | ~r1_xboole_0(B_86, D_87) | ~r1_tarski(C_85, D_87) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 34.82/25.20  tff(c_392, plain, (![C_165, C_161, B_163, A_164, A_162]: (r1_xboole_0(A_162, C_161) | ~r1_tarski(C_161, k4_xboole_0(C_165, B_163)) | ~r1_tarski(A_162, A_164) | ~r1_tarski(A_164, B_163))), inference(resolution, [status(thm)], [c_12, c_172])).
% 34.82/25.20  tff(c_416, plain, (![B_166, A_167, A_169, C_168, B_170]: (r1_xboole_0(A_169, k4_xboole_0(k4_xboole_0(C_168, B_166), B_170)) | ~r1_tarski(A_169, A_167) | ~r1_tarski(A_167, B_166))), inference(resolution, [status(thm)], [c_2, c_392])).
% 34.82/25.20  tff(c_4914, plain, (![A_806, B_801, B_805, B_802, B_803, C_804]: (r1_xboole_0(A_806, k4_xboole_0(k4_xboole_0(C_804, B_802), B_803)) | ~r1_tarski(k2_xboole_0(B_805, k2_xboole_0(B_801, k4_xboole_0(A_806, B_805))), B_802))), inference(resolution, [status(thm)], [c_56, c_416])).
% 34.82/25.20  tff(c_4938, plain, (![A_806, B_801, B_2, B_805, B_803, C_804]: (r1_xboole_0(A_806, k4_xboole_0(k4_xboole_0(C_804, k2_xboole_0(B_2, k2_xboole_0(B_805, k2_xboole_0(B_801, k4_xboole_0(A_806, B_805))))), B_803)))), inference(resolution, [status(thm)], [c_50, c_4914])).
% 34.82/25.20  tff(c_8142, plain, (![C_1047, B_1044, C_1042, A_1046, B_1045, B_1043]: (r1_xboole_0(A_1046, k4_xboole_0(k4_xboole_0(C_1047, B_1043), B_1044)) | ~r1_tarski(k4_xboole_0(B_1045, C_1042), B_1043) | ~r1_xboole_0(A_1046, C_1042) | ~r1_tarski(A_1046, B_1045))), inference(resolution, [status(thm)], [c_14, c_416])).
% 34.82/25.20  tff(c_8227, plain, (![C_1062, B_1064, A_1065, A_1066, B_1063]: (r1_xboole_0(A_1066, k4_xboole_0(k4_xboole_0(C_1062, A_1065), B_1063)) | ~r1_xboole_0(A_1066, B_1064) | ~r1_tarski(A_1066, A_1065))), inference(resolution, [status(thm)], [c_2, c_8142])).
% 34.82/25.20  tff(c_8687, plain, (![A_1067, C_1068, A_1069, B_1070]: (r1_xboole_0(A_1067, k4_xboole_0(k4_xboole_0(C_1068, A_1069), B_1070)) | ~r1_tarski(A_1067, A_1069))), inference(resolution, [status(thm)], [c_4938, c_8227])).
% 34.82/25.20  tff(c_10, plain, (![A_12, C_14, B_13, D_15]: (r1_xboole_0(A_12, C_14) | ~r1_xboole_0(B_13, D_15) | ~r1_tarski(C_14, D_15) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 34.82/25.20  tff(c_25494, plain, (![A_2354, C_2352, A_2355, A_2351, C_2353, B_2350]: (r1_xboole_0(A_2351, C_2352) | ~r1_tarski(C_2352, k4_xboole_0(k4_xboole_0(C_2353, A_2354), B_2350)) | ~r1_tarski(A_2351, A_2355) | ~r1_tarski(A_2355, A_2354))), inference(resolution, [status(thm)], [c_8687, c_10])).
% 34.82/25.20  tff(c_26309, plain, (![A_2410, A_2415, C_2414, B_2412, B_2413, A_2411]: (r1_xboole_0(A_2415, k4_xboole_0(k4_xboole_0(k4_xboole_0(C_2414, A_2411), B_2412), B_2413)) | ~r1_tarski(A_2415, A_2410) | ~r1_tarski(A_2410, A_2411))), inference(resolution, [status(thm)], [c_2, c_25494])).
% 34.82/25.20  tff(c_26435, plain, (![A_2426, C_2424, B_2427, B_2425, B_2428, A_2429]: (r1_xboole_0(A_2429, k4_xboole_0(k4_xboole_0(k4_xboole_0(C_2424, A_2426), B_2427), B_2425)) | ~r1_tarski(k2_xboole_0(B_2428, A_2429), A_2426))), inference(resolution, [status(thm)], [c_50, c_26309])).
% 34.82/25.20  tff(c_26463, plain, (![B_2, C_2424, B_2427, B_2425, B_2428, A_2429]: (r1_xboole_0(A_2429, k4_xboole_0(k4_xboole_0(k4_xboole_0(C_2424, k2_xboole_0(B_2, k2_xboole_0(B_2428, A_2429))), B_2427), B_2425)))), inference(resolution, [status(thm)], [c_50, c_26435])).
% 34.82/25.20  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 34.82/25.20  tff(c_80, plain, (![A_72, B_73]: (r1_tarski(k1_tops_1(A_72, B_73), B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_80])).
% 34.82/25.20  tff(c_87, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_80])).
% 34.82/25.20  tff(c_94, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_87])).
% 34.82/25.20  tff(c_508, plain, (![A_194, C_195, A_196]: (r1_xboole_0(A_194, k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_195))) | ~r1_tarski(A_194, A_196) | ~r1_tarski(A_196, C_195))), inference(resolution, [status(thm)], [c_131, c_392])).
% 34.82/25.20  tff(c_22407, plain, (![A_2025, C_2026, B_2027, B_2028]: (r1_xboole_0(A_2025, k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_2026))) | ~r1_tarski(k2_xboole_0(B_2027, k2_xboole_0(B_2028, k4_xboole_0(A_2025, B_2027))), C_2026))), inference(resolution, [status(thm)], [c_56, c_508])).
% 34.82/25.20  tff(c_22442, plain, (![A_2025, B_2, B_2027, B_2028]: (r1_xboole_0(A_2025, k1_tops_1('#skF_1', k4_xboole_0('#skF_2', k2_xboole_0(B_2, k2_xboole_0(B_2027, k2_xboole_0(B_2028, k4_xboole_0(A_2025, B_2027))))))))), inference(resolution, [status(thm)], [c_50, c_22407])).
% 34.82/25.20  tff(c_57, plain, (![A_60, B_61, B_62]: (r1_tarski(A_60, k2_xboole_0(B_61, k2_xboole_0(B_62, k4_xboole_0(A_60, B_61)))))), inference(resolution, [status(thm)], [c_51, c_6])).
% 34.82/25.20  tff(c_62, plain, (![A_6, B_7, B_61, B_62]: (r1_tarski(A_6, k2_xboole_0(B_7, k2_xboole_0(B_61, k2_xboole_0(B_62, k4_xboole_0(k4_xboole_0(A_6, B_7), B_61))))))), inference(resolution, [status(thm)], [c_57, c_6])).
% 34.82/25.20  tff(c_817, plain, (![A_268, A_267, C_264, B_266, A_265]: (r1_xboole_0(A_268, A_267) | ~r1_tarski(A_268, A_265) | ~r1_tarski(A_265, C_264) | ~r1_xboole_0(A_267, C_264) | ~r1_tarski(A_267, B_266))), inference(resolution, [status(thm)], [c_14, c_392])).
% 34.82/25.20  tff(c_1301, plain, (![B_296, B_297, A_299, A_298, C_295]: (r1_xboole_0(k4_xboole_0(A_299, B_297), A_298) | ~r1_tarski(A_299, C_295) | ~r1_xboole_0(A_298, C_295) | ~r1_tarski(A_298, B_296))), inference(resolution, [status(thm)], [c_2, c_817])).
% 34.82/25.20  tff(c_1564, plain, (![B_322, A_320, B_321, B_324, A_323]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(A_323, B_322), B_321), A_320) | ~r1_xboole_0(A_320, A_323) | ~r1_tarski(A_320, B_324))), inference(resolution, [status(thm)], [c_2, c_1301])).
% 34.82/25.20  tff(c_1619, plain, (![A_325, B_326, B_327, A_328]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(A_325, B_326), B_327), A_328) | ~r1_xboole_0(A_328, A_325))), inference(resolution, [status(thm)], [c_62, c_1564])).
% 34.82/25.20  tff(c_8, plain, (![A_9, C_11, B_10]: (r1_xboole_0(A_9, C_11) | ~r1_xboole_0(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 34.82/25.20  tff(c_1687, plain, (![B_341, A_339, B_342, A_338, A_340]: (r1_xboole_0(A_340, A_339) | ~r1_tarski(A_340, k4_xboole_0(k4_xboole_0(A_338, B_341), B_342)) | ~r1_xboole_0(A_339, A_338))), inference(resolution, [status(thm)], [c_1619, c_8])).
% 34.82/25.20  tff(c_2844, plain, (![A_528, B_526, C_525, A_527, A_529]: (r1_xboole_0(A_527, A_529) | ~r1_xboole_0(A_529, A_528) | ~r1_xboole_0(A_527, C_525) | ~r1_tarski(A_527, k4_xboole_0(A_528, B_526)))), inference(resolution, [status(thm)], [c_14, c_1687])).
% 34.82/25.20  tff(c_44590, plain, (![C_3068, B_3066, A_3071, C_3070, A_3069, B_3067]: (r1_xboole_0(A_3071, A_3069) | ~r1_xboole_0(A_3071, C_3068) | ~r1_tarski(A_3071, k4_xboole_0(k4_xboole_0(C_3070, B_3067), B_3066)) | ~r1_tarski(A_3069, B_3067))), inference(resolution, [status(thm)], [c_12, c_2844])).
% 34.82/25.20  tff(c_45809, plain, (![A_3075, B_3073, B_3074, A_3076, C_3072]: (r1_xboole_0(A_3076, A_3075) | ~r1_tarski(A_3076, k4_xboole_0(k4_xboole_0(C_3072, B_3073), B_3074)) | ~r1_tarski(A_3075, B_3073))), inference(resolution, [status(thm)], [c_22442, c_44590])).
% 34.82/25.20  tff(c_46813, plain, (![B_3124, C_3127, A_3126, C_3123, A_3125]: (r1_xboole_0(A_3125, A_3126) | ~r1_tarski(A_3126, B_3124) | ~r1_xboole_0(A_3125, C_3123) | ~r1_tarski(A_3125, k4_xboole_0(C_3127, B_3124)))), inference(resolution, [status(thm)], [c_14, c_45809])).
% 34.82/25.20  tff(c_46919, plain, (![A_3128, C_3129, C_3130]: (r1_xboole_0(A_3128, k1_tops_1('#skF_1', '#skF_3')) | ~r1_xboole_0(A_3128, C_3129) | ~r1_tarski(A_3128, k4_xboole_0(C_3130, '#skF_3')))), inference(resolution, [status(thm)], [c_94, c_46813])).
% 34.82/25.20  tff(c_48173, plain, (![A_3131, C_3132]: (r1_xboole_0(A_3131, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_3131, k4_xboole_0(C_3132, '#skF_3')))), inference(resolution, [status(thm)], [c_26463, c_46919])).
% 34.82/25.20  tff(c_48215, plain, (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_131, c_48173])).
% 34.82/25.20  tff(c_48241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4420, c_48215])).
% 34.82/25.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.82/25.20  
% 34.82/25.20  Inference rules
% 34.82/25.20  ----------------------
% 34.82/25.20  #Ref     : 0
% 34.82/25.20  #Sup     : 14367
% 34.82/25.20  #Fact    : 0
% 34.82/25.20  #Define  : 0
% 34.82/25.20  #Split   : 11
% 34.82/25.20  #Chain   : 0
% 34.82/25.20  #Close   : 0
% 34.82/25.20  
% 34.82/25.20  Ordering : KBO
% 34.82/25.20  
% 34.82/25.20  Simplification rules
% 34.82/25.20  ----------------------
% 34.82/25.20  #Subsume      : 730
% 34.82/25.20  #Demod        : 3682
% 34.82/25.20  #Tautology    : 177
% 34.82/25.20  #SimpNegUnit  : 9
% 34.82/25.20  #BackRed      : 2
% 34.82/25.20  
% 34.82/25.20  #Partial instantiations: 0
% 34.82/25.20  #Strategies tried      : 1
% 34.82/25.20  
% 34.82/25.20  Timing (in seconds)
% 34.82/25.20  ----------------------
% 34.82/25.20  Preprocessing        : 0.31
% 34.82/25.20  Parsing              : 0.17
% 34.82/25.20  CNF conversion       : 0.02
% 34.82/25.20  Main loop            : 24.11
% 34.82/25.20  Inferencing          : 2.15
% 34.82/25.20  Reduction            : 8.30
% 34.82/25.20  Demodulation         : 7.27
% 34.82/25.20  BG Simplification    : 0.27
% 34.82/25.21  Subsumption          : 12.28
% 34.82/25.21  Abstraction          : 0.37
% 34.82/25.21  MUC search           : 0.00
% 34.82/25.21  Cooper               : 0.00
% 34.82/25.21  Total                : 24.46
% 34.82/25.21  Index Insertion      : 0.00
% 34.82/25.21  Index Deletion       : 0.00
% 34.82/25.21  Index Matching       : 0.00
% 34.82/25.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
