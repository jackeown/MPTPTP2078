%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:57 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 156 expanded)
%              Number of leaves         :   31 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 297 expanded)
%              Number of equality atoms :   48 (  64 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1676,plain,(
    ! [B_221,A_222] :
      ( r1_tarski(B_221,k2_pre_topc(A_222,B_221))
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1678,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1676])).

tff(c_1681,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1678])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1697,plain,(
    k4_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1681,c_6])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = A_42
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_1355,plain,(
    ! [A_167,C_168,B_169] :
      ( r1_xboole_0(A_167,C_168)
      | ~ r1_xboole_0(B_169,C_168)
      | ~ r1_tarski(A_167,B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1369,plain,(
    ! [A_170,A_171] :
      ( r1_xboole_0(A_170,A_171)
      | ~ r1_tarski(A_170,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_47,c_1355])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1391,plain,(
    ! [A_174,A_175] :
      ( k4_xboole_0(A_174,A_175) = A_174
      | ~ r1_tarski(A_174,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1369,c_12])).

tff(c_1394,plain,(
    ! [A_3,A_175] :
      ( k4_xboole_0(A_3,A_175) = A_3
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1391])).

tff(c_1399,plain,(
    ! [A_176,A_177] :
      ( k4_xboole_0(A_176,A_177) = A_176
      | k1_xboole_0 != A_176 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1394])).

tff(c_54,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1338,plain,(
    ! [B_163,A_164] :
      ( r1_xboole_0(B_163,A_164)
      | k4_xboole_0(A_164,B_163) != A_164 ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_1344,plain,(
    ! [B_163,A_164] :
      ( k4_xboole_0(B_163,A_164) = B_163
      | k4_xboole_0(A_164,B_163) != A_164 ) ),
    inference(resolution,[status(thm)],[c_1338,c_12])).

tff(c_1428,plain,(
    ! [A_177] : k4_xboole_0(A_177,k1_xboole_0) = A_177 ),
    inference(superposition,[status(thm),theory(equality)],[c_1399,c_1344])).

tff(c_2092,plain,(
    ! [A_248,B_249] :
      ( m1_subset_1(k2_pre_topc(A_248,B_249),k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k7_subset_1(A_11,B_12,C_13) = k4_xboole_0(B_12,C_13)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2442,plain,(
    ! [A_295,B_296,C_297] :
      ( k7_subset_1(u1_struct_0(A_295),k2_pre_topc(A_295,B_296),C_297) = k4_xboole_0(k2_pre_topc(A_295,B_296),C_297)
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0(A_295)))
      | ~ l1_pre_topc(A_295) ) ),
    inference(resolution,[status(thm)],[c_2092,c_16])).

tff(c_2446,plain,(
    ! [C_297] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_297) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_297)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_2442])).

tff(c_2451,plain,(
    ! [C_298] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_298) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_298) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2446])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_76,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_553,plain,(
    ! [B_104,A_105] :
      ( v2_tops_1(B_104,A_105)
      | k1_tops_1(A_105,B_104) != k1_xboole_0
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_559,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_553])).

tff(c_563,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_559])).

tff(c_564,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_563])).

tff(c_224,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k1_tops_1(A_66,B_67),B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_226,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_224])).

tff(c_229,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_226])).

tff(c_233,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_229,c_6])).

tff(c_669,plain,(
    ! [A_119,B_120] :
      ( r1_xboole_0(k1_tops_1(A_119,B_120),k2_tops_1(A_119,B_120))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1156,plain,(
    ! [A_158,B_159] :
      ( k4_xboole_0(k1_tops_1(A_158,B_159),k2_tops_1(A_158,B_159)) = k1_tops_1(A_158,B_159)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(resolution,[status(thm)],[c_669,c_12])).

tff(c_1160,plain,
    ( k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1156])).

tff(c_1164,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1160])).

tff(c_42,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_111,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_42])).

tff(c_57,plain,(
    ! [B_39,A_38] :
      ( r1_xboole_0(B_39,A_38)
      | k4_xboole_0(A_38,B_39) != A_38 ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_116,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_xboole_0(A_48,C_49)
      | ~ r1_xboole_0(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_490,plain,(
    ! [A_97,A_98,B_99] :
      ( r1_xboole_0(A_97,A_98)
      | ~ r1_tarski(A_97,B_99)
      | k4_xboole_0(A_98,B_99) != A_98 ) ),
    inference(resolution,[status(thm)],[c_57,c_116])).

tff(c_501,plain,(
    ! [A_98] :
      ( r1_xboole_0('#skF_2',A_98)
      | k4_xboole_0(A_98,k2_tops_1('#skF_1','#skF_2')) != A_98 ) ),
    inference(resolution,[status(thm)],[c_111,c_490])).

tff(c_1222,plain,(
    r1_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1164,c_501])).

tff(c_1235,plain,(
    r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1222,c_2])).

tff(c_1296,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1235,c_12])).

tff(c_1301,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_1296])).

tff(c_1303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_564,c_1301])).

tff(c_1305,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2145,plain,(
    ! [A_254,B_255] :
      ( k1_tops_1(A_254,B_255) = k1_xboole_0
      | ~ v2_tops_1(B_255,A_254)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2151,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2145])).

tff(c_2155,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1305,c_2151])).

tff(c_2281,plain,(
    ! [A_265,B_266] :
      ( k7_subset_1(u1_struct_0(A_265),k2_pre_topc(A_265,B_266),k1_tops_1(A_265,B_266)) = k2_tops_1(A_265,B_266)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2290,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2155,c_2281])).

tff(c_2294,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2290])).

tff(c_2457,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2451,c_2294])).

tff(c_2473,plain,(
    k2_tops_1('#skF_1','#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_2457])).

tff(c_1304,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1335,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_1304])).

tff(c_2481,plain,(
    k4_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2473,c_1335])).

tff(c_2485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1697,c_2481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:34:04 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.72  
% 4.36/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.72  %$ v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.36/1.72  
% 4.36/1.72  %Foreground sorts:
% 4.36/1.72  
% 4.36/1.72  
% 4.36/1.72  %Background operators:
% 4.36/1.72  
% 4.36/1.72  
% 4.36/1.72  %Foreground operators:
% 4.36/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.36/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.36/1.72  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.36/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.36/1.72  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.36/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.36/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.36/1.72  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.36/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.36/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.36/1.72  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.36/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.36/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.36/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.36/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.36/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.36/1.72  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.36/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.36/1.72  
% 4.36/1.74  tff(f_102, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 4.36/1.74  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.36/1.74  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.36/1.74  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.36/1.74  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.36/1.74  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.36/1.74  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.36/1.74  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.36/1.74  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.36/1.74  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 4.36/1.74  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.36/1.74  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_1)).
% 4.36/1.74  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.36/1.74  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.36/1.74  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.36/1.74  tff(c_1676, plain, (![B_221, A_222]: (r1_tarski(B_221, k2_pre_topc(A_222, B_221)) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.36/1.74  tff(c_1678, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1676])).
% 4.36/1.74  tff(c_1681, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1678])).
% 4.36/1.74  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.36/1.74  tff(c_1697, plain, (k4_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1681, c_6])).
% 4.36/1.74  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.36/1.74  tff(c_63, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=A_42 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.36/1.74  tff(c_75, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(resolution, [status(thm)], [c_10, c_63])).
% 4.36/1.74  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.36/1.74  tff(c_44, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.36/1.74  tff(c_47, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_10, c_44])).
% 4.36/1.74  tff(c_1355, plain, (![A_167, C_168, B_169]: (r1_xboole_0(A_167, C_168) | ~r1_xboole_0(B_169, C_168) | ~r1_tarski(A_167, B_169))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.36/1.74  tff(c_1369, plain, (![A_170, A_171]: (r1_xboole_0(A_170, A_171) | ~r1_tarski(A_170, k1_xboole_0))), inference(resolution, [status(thm)], [c_47, c_1355])).
% 4.36/1.74  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.36/1.74  tff(c_1391, plain, (![A_174, A_175]: (k4_xboole_0(A_174, A_175)=A_174 | ~r1_tarski(A_174, k1_xboole_0))), inference(resolution, [status(thm)], [c_1369, c_12])).
% 4.36/1.74  tff(c_1394, plain, (![A_3, A_175]: (k4_xboole_0(A_3, A_175)=A_3 | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1391])).
% 4.36/1.74  tff(c_1399, plain, (![A_176, A_177]: (k4_xboole_0(A_176, A_177)=A_176 | k1_xboole_0!=A_176)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1394])).
% 4.36/1.74  tff(c_54, plain, (![A_38, B_39]: (r1_xboole_0(A_38, B_39) | k4_xboole_0(A_38, B_39)!=A_38)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.36/1.74  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.36/1.74  tff(c_1338, plain, (![B_163, A_164]: (r1_xboole_0(B_163, A_164) | k4_xboole_0(A_164, B_163)!=A_164)), inference(resolution, [status(thm)], [c_54, c_2])).
% 4.36/1.74  tff(c_1344, plain, (![B_163, A_164]: (k4_xboole_0(B_163, A_164)=B_163 | k4_xboole_0(A_164, B_163)!=A_164)), inference(resolution, [status(thm)], [c_1338, c_12])).
% 4.36/1.74  tff(c_1428, plain, (![A_177]: (k4_xboole_0(A_177, k1_xboole_0)=A_177)), inference(superposition, [status(thm), theory('equality')], [c_1399, c_1344])).
% 4.36/1.74  tff(c_2092, plain, (![A_248, B_249]: (m1_subset_1(k2_pre_topc(A_248, B_249), k1_zfmisc_1(u1_struct_0(A_248))) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_pre_topc(A_248))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.36/1.74  tff(c_16, plain, (![A_11, B_12, C_13]: (k7_subset_1(A_11, B_12, C_13)=k4_xboole_0(B_12, C_13) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.36/1.74  tff(c_2442, plain, (![A_295, B_296, C_297]: (k7_subset_1(u1_struct_0(A_295), k2_pre_topc(A_295, B_296), C_297)=k4_xboole_0(k2_pre_topc(A_295, B_296), C_297) | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0(A_295))) | ~l1_pre_topc(A_295))), inference(resolution, [status(thm)], [c_2092, c_16])).
% 4.36/1.74  tff(c_2446, plain, (![C_297]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_297)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_297) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_2442])).
% 4.36/1.74  tff(c_2451, plain, (![C_298]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_298)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_298))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2446])).
% 4.36/1.74  tff(c_36, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.36/1.74  tff(c_76, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 4.36/1.74  tff(c_553, plain, (![B_104, A_105]: (v2_tops_1(B_104, A_105) | k1_tops_1(A_105, B_104)!=k1_xboole_0 | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.36/1.74  tff(c_559, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_553])).
% 4.36/1.74  tff(c_563, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_559])).
% 4.36/1.74  tff(c_564, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_76, c_563])).
% 4.36/1.74  tff(c_224, plain, (![A_66, B_67]: (r1_tarski(k1_tops_1(A_66, B_67), B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.36/1.74  tff(c_226, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_224])).
% 4.36/1.74  tff(c_229, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_226])).
% 4.36/1.74  tff(c_233, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_229, c_6])).
% 4.36/1.74  tff(c_669, plain, (![A_119, B_120]: (r1_xboole_0(k1_tops_1(A_119, B_120), k2_tops_1(A_119, B_120)) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.36/1.74  tff(c_1156, plain, (![A_158, B_159]: (k4_xboole_0(k1_tops_1(A_158, B_159), k2_tops_1(A_158, B_159))=k1_tops_1(A_158, B_159) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(resolution, [status(thm)], [c_669, c_12])).
% 4.36/1.74  tff(c_1160, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1156])).
% 4.36/1.74  tff(c_1164, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1160])).
% 4.36/1.74  tff(c_42, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.36/1.74  tff(c_111, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_76, c_42])).
% 4.36/1.74  tff(c_57, plain, (![B_39, A_38]: (r1_xboole_0(B_39, A_38) | k4_xboole_0(A_38, B_39)!=A_38)), inference(resolution, [status(thm)], [c_54, c_2])).
% 4.36/1.74  tff(c_116, plain, (![A_48, C_49, B_50]: (r1_xboole_0(A_48, C_49) | ~r1_xboole_0(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.36/1.74  tff(c_490, plain, (![A_97, A_98, B_99]: (r1_xboole_0(A_97, A_98) | ~r1_tarski(A_97, B_99) | k4_xboole_0(A_98, B_99)!=A_98)), inference(resolution, [status(thm)], [c_57, c_116])).
% 4.36/1.74  tff(c_501, plain, (![A_98]: (r1_xboole_0('#skF_2', A_98) | k4_xboole_0(A_98, k2_tops_1('#skF_1', '#skF_2'))!=A_98)), inference(resolution, [status(thm)], [c_111, c_490])).
% 4.36/1.74  tff(c_1222, plain, (r1_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1164, c_501])).
% 4.36/1.74  tff(c_1235, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1222, c_2])).
% 4.36/1.74  tff(c_1296, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1235, c_12])).
% 4.36/1.74  tff(c_1301, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_233, c_1296])).
% 4.36/1.74  tff(c_1303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_564, c_1301])).
% 4.36/1.74  tff(c_1305, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 4.36/1.74  tff(c_2145, plain, (![A_254, B_255]: (k1_tops_1(A_254, B_255)=k1_xboole_0 | ~v2_tops_1(B_255, A_254) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_pre_topc(A_254))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.36/1.74  tff(c_2151, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2145])).
% 4.36/1.74  tff(c_2155, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1305, c_2151])).
% 4.36/1.74  tff(c_2281, plain, (![A_265, B_266]: (k7_subset_1(u1_struct_0(A_265), k2_pre_topc(A_265, B_266), k1_tops_1(A_265, B_266))=k2_tops_1(A_265, B_266) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.36/1.74  tff(c_2290, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2155, c_2281])).
% 4.36/1.74  tff(c_2294, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2290])).
% 4.36/1.74  tff(c_2457, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2451, c_2294])).
% 4.36/1.74  tff(c_2473, plain, (k2_tops_1('#skF_1', '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_2457])).
% 4.36/1.74  tff(c_1304, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 4.36/1.74  tff(c_1335, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_1304])).
% 4.36/1.74  tff(c_2481, plain, (k4_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2473, c_1335])).
% 4.36/1.74  tff(c_2485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1697, c_2481])).
% 4.36/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.74  
% 4.36/1.74  Inference rules
% 4.36/1.74  ----------------------
% 4.36/1.74  #Ref     : 1
% 4.36/1.74  #Sup     : 634
% 4.36/1.74  #Fact    : 0
% 4.36/1.74  #Define  : 0
% 4.36/1.74  #Split   : 16
% 4.36/1.74  #Chain   : 0
% 4.36/1.74  #Close   : 0
% 4.36/1.74  
% 4.36/1.74  Ordering : KBO
% 4.36/1.74  
% 4.36/1.74  Simplification rules
% 4.36/1.74  ----------------------
% 4.36/1.74  #Subsume      : 309
% 4.36/1.74  #Demod        : 170
% 4.36/1.74  #Tautology    : 171
% 4.36/1.74  #SimpNegUnit  : 19
% 4.36/1.74  #BackRed      : 23
% 4.36/1.74  
% 4.36/1.74  #Partial instantiations: 0
% 4.36/1.74  #Strategies tried      : 1
% 4.36/1.74  
% 4.36/1.74  Timing (in seconds)
% 4.36/1.74  ----------------------
% 4.36/1.74  Preprocessing        : 0.33
% 4.36/1.74  Parsing              : 0.18
% 4.36/1.74  CNF conversion       : 0.02
% 4.36/1.74  Main loop            : 0.70
% 4.36/1.74  Inferencing          : 0.24
% 4.36/1.74  Reduction            : 0.21
% 4.36/1.74  Demodulation         : 0.14
% 4.36/1.74  BG Simplification    : 0.03
% 4.36/1.74  Subsumption          : 0.17
% 4.36/1.74  Abstraction          : 0.04
% 4.36/1.74  MUC search           : 0.00
% 4.36/1.74  Cooper               : 0.00
% 4.36/1.74  Total                : 1.06
% 4.36/1.74  Index Insertion      : 0.00
% 4.36/1.74  Index Deletion       : 0.00
% 4.36/1.74  Index Matching       : 0.00
% 4.36/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
