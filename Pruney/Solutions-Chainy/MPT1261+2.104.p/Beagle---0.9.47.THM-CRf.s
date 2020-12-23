%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:26 EST 2020

% Result     : Theorem 5.81s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 142 expanded)
%              Number of leaves         :   32 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  132 ( 283 expanded)
%              Number of equality atoms :   50 (  87 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
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

tff(f_72,axiom,(
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

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_78,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5729,plain,(
    ! [A_198,B_199,C_200] :
      ( k7_subset_1(A_198,B_199,C_200) = k4_xboole_0(B_199,C_200)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5732,plain,(
    ! [C_200] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_200) = k4_xboole_0('#skF_2',C_200) ),
    inference(resolution,[status(thm)],[c_34,c_5729])).

tff(c_40,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_112,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1495,plain,(
    ! [B_102,A_103] :
      ( v4_pre_topc(B_102,A_103)
      | k2_pre_topc(A_103,B_102) != B_102
      | ~ v2_pre_topc(A_103)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1501,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1495])).

tff(c_1505,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_1501])).

tff(c_1506,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1505])).

tff(c_1809,plain,(
    ! [A_107,B_108] :
      ( k4_subset_1(u1_struct_0(A_107),B_108,k2_tops_1(A_107,B_108)) = k2_pre_topc(A_107,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1813,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1809])).

tff(c_1817,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1813])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [A_48,B_49,C_50] :
      ( r1_tarski(A_48,k2_xboole_0(B_49,C_50))
      | ~ r1_tarski(k4_xboole_0(A_48,B_49),C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_128,plain,(
    ! [A_48,B_49] : r1_tarski(A_48,k2_xboole_0(B_49,k4_xboole_0(A_48,B_49))) ),
    inference(resolution,[status(thm)],[c_8,c_121])).

tff(c_131,plain,(
    ! [A_48,B_49] : r1_tarski(A_48,k2_xboole_0(B_49,A_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_128])).

tff(c_187,plain,(
    ! [A_55,B_56,C_57] :
      ( k7_subset_1(A_55,B_56,C_57) = k4_xboole_0(B_56,C_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_375,plain,(
    ! [C_69] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_69) = k4_xboole_0('#skF_2',C_69) ),
    inference(resolution,[status(thm)],[c_34,c_187])).

tff(c_46,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_229,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_46])).

tff(c_381,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_229])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(k4_xboole_0(A_9,B_10),C_11)
      | ~ r1_tarski(A_9,k2_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1635,plain,(
    ! [C_106] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),C_106)
      | ~ r1_tarski('#skF_2',k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_14])).

tff(c_1688,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_131,c_1635])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1695,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1688,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_132,plain,(
    ! [A_51,B_52] : r1_tarski(A_51,k2_xboole_0(B_52,A_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_128])).

tff(c_158,plain,(
    ! [B_53,A_54] : r1_tarski(B_53,k2_xboole_0(B_53,A_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_132])).

tff(c_700,plain,(
    ! [B_82,A_83] : k2_xboole_0(B_82,k2_xboole_0(B_82,A_83)) = k2_xboole_0(B_82,A_83) ),
    inference(resolution,[status(thm)],[c_158,c_10])).

tff(c_774,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_700])).

tff(c_1705,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1695,c_774])).

tff(c_1749,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1705])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_tops_1(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1320,plain,(
    ! [A_96,B_97,C_98] :
      ( k4_subset_1(A_96,B_97,C_98) = k2_xboole_0(B_97,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5474,plain,(
    ! [A_177,B_178,B_179] :
      ( k4_subset_1(u1_struct_0(A_177),B_178,k2_tops_1(A_177,B_179)) = k2_xboole_0(B_178,k2_tops_1(A_177,B_179))
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(resolution,[status(thm)],[c_26,c_1320])).

tff(c_5478,plain,(
    ! [B_179] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_179)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_179))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_5474])).

tff(c_5532,plain,(
    ! [B_182] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_182)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_182))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5478])).

tff(c_5539,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_5532])).

tff(c_5544,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1817,c_1749,c_5539])).

tff(c_5546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1506,c_5544])).

tff(c_5547,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5801,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5732,c_5547])).

tff(c_5548,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5882,plain,(
    ! [A_212,B_213] :
      ( k2_pre_topc(A_212,B_213) = B_213
      | ~ v4_pre_topc(B_213,A_212)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5888,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_5882])).

tff(c_5892,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5548,c_5888])).

tff(c_7331,plain,(
    ! [A_249,B_250] :
      ( k7_subset_1(u1_struct_0(A_249),k2_pre_topc(A_249,B_250),k1_tops_1(A_249,B_250)) = k2_tops_1(A_249,B_250)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7340,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5892,c_7331])).

tff(c_7344,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_5732,c_7340])).

tff(c_7346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5801,c_7344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:38 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.81/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.19  
% 5.81/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.19  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 5.81/2.19  
% 5.81/2.19  %Foreground sorts:
% 5.81/2.19  
% 5.81/2.19  
% 5.81/2.19  %Background operators:
% 5.81/2.19  
% 5.81/2.19  
% 5.81/2.19  %Foreground operators:
% 5.81/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.81/2.19  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.81/2.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.81/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.81/2.19  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.81/2.19  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.81/2.19  tff('#skF_2', type, '#skF_2': $i).
% 5.81/2.19  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.81/2.19  tff('#skF_1', type, '#skF_1': $i).
% 5.81/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.81/2.19  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.81/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.81/2.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.81/2.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.81/2.19  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.81/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.81/2.19  
% 5.81/2.21  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.81/2.21  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.81/2.21  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.81/2.21  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.81/2.21  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.81/2.21  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.81/2.21  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.81/2.21  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.81/2.21  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.81/2.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.81/2.21  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.81/2.21  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.81/2.21  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.81/2.21  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.81/2.21  tff(c_5729, plain, (![A_198, B_199, C_200]: (k7_subset_1(A_198, B_199, C_200)=k4_xboole_0(B_199, C_200) | ~m1_subset_1(B_199, k1_zfmisc_1(A_198)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.81/2.21  tff(c_5732, plain, (![C_200]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_200)=k4_xboole_0('#skF_2', C_200))), inference(resolution, [status(thm)], [c_34, c_5729])).
% 5.81/2.21  tff(c_40, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.81/2.21  tff(c_112, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 5.81/2.21  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.81/2.21  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.81/2.21  tff(c_1495, plain, (![B_102, A_103]: (v4_pre_topc(B_102, A_103) | k2_pre_topc(A_103, B_102)!=B_102 | ~v2_pre_topc(A_103) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.81/2.21  tff(c_1501, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1495])).
% 5.81/2.21  tff(c_1505, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_1501])).
% 5.81/2.21  tff(c_1506, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_112, c_1505])).
% 5.81/2.21  tff(c_1809, plain, (![A_107, B_108]: (k4_subset_1(u1_struct_0(A_107), B_108, k2_tops_1(A_107, B_108))=k2_pre_topc(A_107, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.81/2.21  tff(c_1813, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1809])).
% 5.81/2.21  tff(c_1817, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1813])).
% 5.81/2.21  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.81/2.21  tff(c_82, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.81/2.21  tff(c_86, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_82])).
% 5.81/2.21  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.81/2.21  tff(c_121, plain, (![A_48, B_49, C_50]: (r1_tarski(A_48, k2_xboole_0(B_49, C_50)) | ~r1_tarski(k4_xboole_0(A_48, B_49), C_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.81/2.21  tff(c_128, plain, (![A_48, B_49]: (r1_tarski(A_48, k2_xboole_0(B_49, k4_xboole_0(A_48, B_49))))), inference(resolution, [status(thm)], [c_8, c_121])).
% 5.81/2.21  tff(c_131, plain, (![A_48, B_49]: (r1_tarski(A_48, k2_xboole_0(B_49, A_48)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_128])).
% 5.81/2.21  tff(c_187, plain, (![A_55, B_56, C_57]: (k7_subset_1(A_55, B_56, C_57)=k4_xboole_0(B_56, C_57) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.81/2.21  tff(c_375, plain, (![C_69]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_69)=k4_xboole_0('#skF_2', C_69))), inference(resolution, [status(thm)], [c_34, c_187])).
% 5.81/2.21  tff(c_46, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.81/2.21  tff(c_229, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_112, c_46])).
% 5.81/2.21  tff(c_381, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_375, c_229])).
% 5.81/2.21  tff(c_14, plain, (![A_9, B_10, C_11]: (r1_tarski(k4_xboole_0(A_9, B_10), C_11) | ~r1_tarski(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.81/2.21  tff(c_1635, plain, (![C_106]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), C_106) | ~r1_tarski('#skF_2', k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_106)))), inference(superposition, [status(thm), theory('equality')], [c_381, c_14])).
% 5.81/2.21  tff(c_1688, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_131, c_1635])).
% 5.81/2.21  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.81/2.21  tff(c_1695, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_1688, c_10])).
% 5.81/2.21  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.81/2.21  tff(c_132, plain, (![A_51, B_52]: (r1_tarski(A_51, k2_xboole_0(B_52, A_51)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_128])).
% 5.81/2.21  tff(c_158, plain, (![B_53, A_54]: (r1_tarski(B_53, k2_xboole_0(B_53, A_54)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_132])).
% 5.81/2.21  tff(c_700, plain, (![B_82, A_83]: (k2_xboole_0(B_82, k2_xboole_0(B_82, A_83))=k2_xboole_0(B_82, A_83))), inference(resolution, [status(thm)], [c_158, c_10])).
% 5.81/2.21  tff(c_774, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_700])).
% 5.81/2.21  tff(c_1705, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1695, c_774])).
% 5.81/2.21  tff(c_1749, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1705])).
% 5.81/2.21  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(k2_tops_1(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.81/2.21  tff(c_1320, plain, (![A_96, B_97, C_98]: (k4_subset_1(A_96, B_97, C_98)=k2_xboole_0(B_97, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.81/2.21  tff(c_5474, plain, (![A_177, B_178, B_179]: (k4_subset_1(u1_struct_0(A_177), B_178, k2_tops_1(A_177, B_179))=k2_xboole_0(B_178, k2_tops_1(A_177, B_179)) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(resolution, [status(thm)], [c_26, c_1320])).
% 5.81/2.21  tff(c_5478, plain, (![B_179]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_179))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_179)) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_5474])).
% 5.81/2.21  tff(c_5532, plain, (![B_182]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_182))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_182)) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5478])).
% 5.81/2.21  tff(c_5539, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_5532])).
% 5.81/2.21  tff(c_5544, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1817, c_1749, c_5539])).
% 5.81/2.21  tff(c_5546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1506, c_5544])).
% 5.81/2.21  tff(c_5547, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 5.81/2.21  tff(c_5801, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5732, c_5547])).
% 5.81/2.21  tff(c_5548, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 5.81/2.21  tff(c_5882, plain, (![A_212, B_213]: (k2_pre_topc(A_212, B_213)=B_213 | ~v4_pre_topc(B_213, A_212) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.81/2.21  tff(c_5888, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_5882])).
% 5.81/2.21  tff(c_5892, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5548, c_5888])).
% 5.81/2.21  tff(c_7331, plain, (![A_249, B_250]: (k7_subset_1(u1_struct_0(A_249), k2_pre_topc(A_249, B_250), k1_tops_1(A_249, B_250))=k2_tops_1(A_249, B_250) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.81/2.21  tff(c_7340, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5892, c_7331])).
% 5.81/2.21  tff(c_7344, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_5732, c_7340])).
% 5.81/2.21  tff(c_7346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5801, c_7344])).
% 5.81/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.21  
% 5.81/2.21  Inference rules
% 5.81/2.21  ----------------------
% 5.81/2.21  #Ref     : 0
% 5.81/2.21  #Sup     : 1805
% 5.81/2.21  #Fact    : 0
% 5.81/2.21  #Define  : 0
% 5.81/2.21  #Split   : 2
% 5.81/2.21  #Chain   : 0
% 5.81/2.21  #Close   : 0
% 5.81/2.21  
% 5.81/2.21  Ordering : KBO
% 5.81/2.21  
% 5.81/2.21  Simplification rules
% 5.81/2.21  ----------------------
% 5.81/2.21  #Subsume      : 72
% 5.81/2.21  #Demod        : 1878
% 5.81/2.21  #Tautology    : 1190
% 5.81/2.21  #SimpNegUnit  : 5
% 5.81/2.21  #BackRed      : 5
% 5.81/2.21  
% 5.81/2.21  #Partial instantiations: 0
% 5.81/2.21  #Strategies tried      : 1
% 5.81/2.21  
% 5.81/2.21  Timing (in seconds)
% 5.81/2.21  ----------------------
% 5.81/2.21  Preprocessing        : 0.33
% 5.81/2.21  Parsing              : 0.18
% 5.81/2.21  CNF conversion       : 0.02
% 5.81/2.21  Main loop            : 1.10
% 5.81/2.21  Inferencing          : 0.33
% 5.81/2.21  Reduction            : 0.50
% 5.81/2.21  Demodulation         : 0.42
% 5.81/2.21  BG Simplification    : 0.04
% 5.81/2.21  Subsumption          : 0.16
% 5.81/2.21  Abstraction          : 0.06
% 5.81/2.21  MUC search           : 0.00
% 5.81/2.21  Cooper               : 0.00
% 5.81/2.21  Total                : 1.48
% 5.81/2.21  Index Insertion      : 0.00
% 5.81/2.21  Index Deletion       : 0.00
% 5.81/2.21  Index Matching       : 0.00
% 5.81/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
