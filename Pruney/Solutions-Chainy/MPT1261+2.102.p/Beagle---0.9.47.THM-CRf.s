%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:26 EST 2020

% Result     : Theorem 5.21s
% Output     : CNFRefutation 5.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 216 expanded)
%              Number of leaves         :   43 (  92 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 421 expanded)
%              Number of equality atoms :   48 ( 108 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1532,plain,(
    ! [A_219,B_220,C_221] :
      ( k7_subset_1(A_219,B_220,C_221) = k4_xboole_0(B_220,C_221)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(A_219)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1538,plain,(
    ! [C_221] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_221) = k4_xboole_0('#skF_2',C_221) ),
    inference(resolution,[status(thm)],[c_50,c_1532])).

tff(c_62,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_130,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_178,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_885,plain,(
    ! [A_161,B_162] :
      ( k4_subset_1(u1_struct_0(A_161),B_162,k2_tops_1(A_161,B_162)) = k2_pre_topc(A_161,B_162)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_906,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_885])).

tff(c_925,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_906])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(A_49,k1_zfmisc_1(B_50))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_201,plain,(
    ! [A_92,B_93,C_94] :
      ( k7_subset_1(A_92,B_93,C_94) = k4_xboole_0(B_93,C_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_235,plain,(
    ! [C_98] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_98) = k4_xboole_0('#skF_2',C_98) ),
    inference(resolution,[status(thm)],[c_50,c_201])).

tff(c_244,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_130])).

tff(c_502,plain,(
    ! [B_128,A_129,C_130] :
      ( k7_subset_1(B_128,A_129,C_130) = k4_xboole_0(A_129,C_130)
      | ~ r1_tarski(A_129,B_128) ) ),
    inference(resolution,[status(thm)],[c_38,c_201])).

tff(c_528,plain,(
    ! [B_131,C_132] : k7_subset_1(B_131,B_131,C_132) = k4_xboole_0(B_131,C_132) ),
    inference(resolution,[status(thm)],[c_8,c_502])).

tff(c_208,plain,(
    ! [A_95,B_96,C_97] :
      ( m1_subset_1(k7_subset_1(A_95,B_96,C_97),k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_218,plain,(
    ! [A_95,B_96,C_97] :
      ( r1_tarski(k7_subset_1(A_95,B_96,C_97),A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(resolution,[status(thm)],[c_208,c_36])).

tff(c_543,plain,(
    ! [B_133,C_134] :
      ( r1_tarski(k4_xboole_0(B_133,C_134),B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(B_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_218])).

tff(c_553,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_543])).

tff(c_558,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_553])).

tff(c_561,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_558])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_561])).

tff(c_566,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_553])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_595,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_566,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_599,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_2])).

tff(c_216,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_208])).

tff(c_220,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_216])).

tff(c_227,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_220,c_36])).

tff(c_770,plain,(
    ! [A_154,B_155,C_156] :
      ( k4_subset_1(A_154,B_155,C_156) = k2_xboole_0(B_155,C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(A_154))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1324,plain,(
    ! [B_197,B_198,A_199] :
      ( k4_subset_1(B_197,B_198,A_199) = k2_xboole_0(B_198,A_199)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(B_197))
      | ~ r1_tarski(A_199,B_197) ) ),
    inference(resolution,[status(thm)],[c_38,c_770])).

tff(c_1403,plain,(
    ! [A_202] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_202) = k2_xboole_0('#skF_2',A_202)
      | ~ r1_tarski(A_202,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_50,c_1324])).

tff(c_1427,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_227,c_1403])).

tff(c_1446,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_599,c_1427])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_363,plain,(
    ! [A_109,B_110] :
      ( v4_pre_topc(k2_pre_topc(A_109,B_110),A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_375,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_363])).

tff(c_386,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_375])).

tff(c_1452,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_386])).

tff(c_1454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_1452])).

tff(c_1455,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_1455])).

tff(c_1472,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1494,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1472,c_56])).

tff(c_1539,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1538,c_1494])).

tff(c_2013,plain,(
    ! [A_294,B_295] :
      ( r1_tarski(k2_tops_1(A_294,B_295),B_295)
      | ~ v4_pre_topc(B_295,A_294)
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0(A_294)))
      | ~ l1_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2030,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2013])).

tff(c_2043,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1472,c_2030])).

tff(c_2053,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2043,c_12])).

tff(c_2057,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2053,c_2])).

tff(c_2209,plain,(
    ! [A_312,B_313] :
      ( k4_subset_1(u1_struct_0(A_312),B_313,k2_tops_1(A_312,B_313)) = k2_pre_topc(A_312,B_313)
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0(A_312)))
      | ~ l1_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2226,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2209])).

tff(c_2239,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2226])).

tff(c_1771,plain,(
    ! [A_266,B_267] :
      ( m1_subset_1(k2_tops_1(A_266,B_267),k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1778,plain,(
    ! [A_266,B_267] :
      ( r1_tarski(k2_tops_1(A_266,B_267),u1_struct_0(A_266))
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(resolution,[status(thm)],[c_1771,c_36])).

tff(c_1892,plain,(
    ! [A_283,B_284,C_285] :
      ( k4_subset_1(A_283,B_284,C_285) = k2_xboole_0(B_284,C_285)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(A_283))
      | ~ m1_subset_1(B_284,k1_zfmisc_1(A_283)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2184,plain,(
    ! [B_309,B_310,A_311] :
      ( k4_subset_1(B_309,B_310,A_311) = k2_xboole_0(B_310,A_311)
      | ~ m1_subset_1(B_310,k1_zfmisc_1(B_309))
      | ~ r1_tarski(A_311,B_309) ) ),
    inference(resolution,[status(thm)],[c_38,c_1892])).

tff(c_2244,plain,(
    ! [A_314] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_314) = k2_xboole_0('#skF_2',A_314)
      | ~ r1_tarski(A_314,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_50,c_2184])).

tff(c_2248,plain,(
    ! [B_267] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_267)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_267))
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1778,c_2244])).

tff(c_3090,plain,(
    ! [B_384] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_384)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_384))
      | ~ m1_subset_1(B_384,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2248])).

tff(c_3118,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_3090])).

tff(c_3131,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_2239,c_3118])).

tff(c_44,plain,(
    ! [A_55,B_57] :
      ( k7_subset_1(u1_struct_0(A_55),k2_pre_topc(A_55,B_57),k1_tops_1(A_55,B_57)) = k2_tops_1(A_55,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3138,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3131,c_44])).

tff(c_3145,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1538,c_3138])).

tff(c_3147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1539,c_3145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n015.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 10:52:23 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.21/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/2.02  
% 5.21/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/2.02  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 5.21/2.02  
% 5.21/2.02  %Foreground sorts:
% 5.21/2.02  
% 5.21/2.02  
% 5.21/2.02  %Background operators:
% 5.21/2.02  
% 5.21/2.02  
% 5.21/2.02  %Foreground operators:
% 5.21/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.21/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.21/2.02  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.21/2.02  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.21/2.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.21/2.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.21/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.21/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.21/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.21/2.02  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.21/2.02  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.21/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.21/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.21/2.02  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.21/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.21/2.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.21/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.21/2.02  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.21/2.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.21/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.21/2.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.21/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.21/2.02  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.21/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.21/2.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.21/2.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.21/2.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.21/2.02  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.21/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.21/2.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.21/2.02  
% 5.21/2.04  tff(f_122, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.21/2.04  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.21/2.04  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.21/2.04  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.21/2.04  tff(f_73, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.21/2.04  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 5.21/2.04  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.21/2.04  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.21/2.04  tff(f_63, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.21/2.04  tff(f_87, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 5.21/2.04  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 5.21/2.04  tff(f_79, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.21/2.04  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.21/2.04  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.21/2.04  tff(c_1532, plain, (![A_219, B_220, C_221]: (k7_subset_1(A_219, B_220, C_221)=k4_xboole_0(B_220, C_221) | ~m1_subset_1(B_220, k1_zfmisc_1(A_219)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.21/2.04  tff(c_1538, plain, (![C_221]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_221)=k4_xboole_0('#skF_2', C_221))), inference(resolution, [status(thm)], [c_50, c_1532])).
% 5.21/2.04  tff(c_62, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.21/2.04  tff(c_130, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 5.21/2.04  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.21/2.04  tff(c_178, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 5.21/2.04  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.21/2.04  tff(c_885, plain, (![A_161, B_162]: (k4_subset_1(u1_struct_0(A_161), B_162, k2_tops_1(A_161, B_162))=k2_pre_topc(A_161, B_162) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.21/2.04  tff(c_906, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_885])).
% 5.21/2.04  tff(c_925, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_906])).
% 5.21/2.04  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.21/2.04  tff(c_38, plain, (![A_49, B_50]: (m1_subset_1(A_49, k1_zfmisc_1(B_50)) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.21/2.04  tff(c_201, plain, (![A_92, B_93, C_94]: (k7_subset_1(A_92, B_93, C_94)=k4_xboole_0(B_93, C_94) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.21/2.04  tff(c_235, plain, (![C_98]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_98)=k4_xboole_0('#skF_2', C_98))), inference(resolution, [status(thm)], [c_50, c_201])).
% 5.21/2.04  tff(c_244, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_235, c_130])).
% 5.21/2.04  tff(c_502, plain, (![B_128, A_129, C_130]: (k7_subset_1(B_128, A_129, C_130)=k4_xboole_0(A_129, C_130) | ~r1_tarski(A_129, B_128))), inference(resolution, [status(thm)], [c_38, c_201])).
% 5.21/2.04  tff(c_528, plain, (![B_131, C_132]: (k7_subset_1(B_131, B_131, C_132)=k4_xboole_0(B_131, C_132))), inference(resolution, [status(thm)], [c_8, c_502])).
% 5.21/2.04  tff(c_208, plain, (![A_95, B_96, C_97]: (m1_subset_1(k7_subset_1(A_95, B_96, C_97), k1_zfmisc_1(A_95)) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.21/2.04  tff(c_36, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.21/2.04  tff(c_218, plain, (![A_95, B_96, C_97]: (r1_tarski(k7_subset_1(A_95, B_96, C_97), A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(resolution, [status(thm)], [c_208, c_36])).
% 5.21/2.04  tff(c_543, plain, (![B_133, C_134]: (r1_tarski(k4_xboole_0(B_133, C_134), B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(B_133)))), inference(superposition, [status(thm), theory('equality')], [c_528, c_218])).
% 5.21/2.04  tff(c_553, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_244, c_543])).
% 5.21/2.04  tff(c_558, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_553])).
% 5.21/2.04  tff(c_561, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_558])).
% 5.21/2.04  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_561])).
% 5.21/2.04  tff(c_566, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_553])).
% 5.21/2.04  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.21/2.04  tff(c_595, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_566, c_12])).
% 5.21/2.04  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.21/2.04  tff(c_599, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_595, c_2])).
% 5.21/2.04  tff(c_216, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_130, c_208])).
% 5.21/2.04  tff(c_220, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_216])).
% 5.21/2.04  tff(c_227, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_220, c_36])).
% 5.21/2.04  tff(c_770, plain, (![A_154, B_155, C_156]: (k4_subset_1(A_154, B_155, C_156)=k2_xboole_0(B_155, C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(A_154)) | ~m1_subset_1(B_155, k1_zfmisc_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.21/2.04  tff(c_1324, plain, (![B_197, B_198, A_199]: (k4_subset_1(B_197, B_198, A_199)=k2_xboole_0(B_198, A_199) | ~m1_subset_1(B_198, k1_zfmisc_1(B_197)) | ~r1_tarski(A_199, B_197))), inference(resolution, [status(thm)], [c_38, c_770])).
% 5.21/2.04  tff(c_1403, plain, (![A_202]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_202)=k2_xboole_0('#skF_2', A_202) | ~r1_tarski(A_202, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_50, c_1324])).
% 5.21/2.04  tff(c_1427, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_227, c_1403])).
% 5.21/2.04  tff(c_1446, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_925, c_599, c_1427])).
% 5.21/2.04  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.21/2.04  tff(c_363, plain, (![A_109, B_110]: (v4_pre_topc(k2_pre_topc(A_109, B_110), A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.21/2.04  tff(c_375, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_363])).
% 5.21/2.04  tff(c_386, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_375])).
% 5.21/2.04  tff(c_1452, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_386])).
% 5.21/2.04  tff(c_1454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_1452])).
% 5.21/2.04  tff(c_1455, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 5.21/2.04  tff(c_1471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_1455])).
% 5.21/2.04  tff(c_1472, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 5.21/2.04  tff(c_1494, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1472, c_56])).
% 5.21/2.04  tff(c_1539, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1538, c_1494])).
% 5.21/2.04  tff(c_2013, plain, (![A_294, B_295]: (r1_tarski(k2_tops_1(A_294, B_295), B_295) | ~v4_pre_topc(B_295, A_294) | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0(A_294))) | ~l1_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.21/2.04  tff(c_2030, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2013])).
% 5.21/2.04  tff(c_2043, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1472, c_2030])).
% 5.21/2.04  tff(c_2053, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_2043, c_12])).
% 5.21/2.04  tff(c_2057, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2053, c_2])).
% 5.21/2.04  tff(c_2209, plain, (![A_312, B_313]: (k4_subset_1(u1_struct_0(A_312), B_313, k2_tops_1(A_312, B_313))=k2_pre_topc(A_312, B_313) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0(A_312))) | ~l1_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.21/2.04  tff(c_2226, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2209])).
% 5.21/2.04  tff(c_2239, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2226])).
% 5.21/2.04  tff(c_1771, plain, (![A_266, B_267]: (m1_subset_1(k2_tops_1(A_266, B_267), k1_zfmisc_1(u1_struct_0(A_266))) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.21/2.04  tff(c_1778, plain, (![A_266, B_267]: (r1_tarski(k2_tops_1(A_266, B_267), u1_struct_0(A_266)) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(resolution, [status(thm)], [c_1771, c_36])).
% 5.21/2.04  tff(c_1892, plain, (![A_283, B_284, C_285]: (k4_subset_1(A_283, B_284, C_285)=k2_xboole_0(B_284, C_285) | ~m1_subset_1(C_285, k1_zfmisc_1(A_283)) | ~m1_subset_1(B_284, k1_zfmisc_1(A_283)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.21/2.04  tff(c_2184, plain, (![B_309, B_310, A_311]: (k4_subset_1(B_309, B_310, A_311)=k2_xboole_0(B_310, A_311) | ~m1_subset_1(B_310, k1_zfmisc_1(B_309)) | ~r1_tarski(A_311, B_309))), inference(resolution, [status(thm)], [c_38, c_1892])).
% 5.21/2.04  tff(c_2244, plain, (![A_314]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_314)=k2_xboole_0('#skF_2', A_314) | ~r1_tarski(A_314, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_50, c_2184])).
% 5.21/2.04  tff(c_2248, plain, (![B_267]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_267))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_267)) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_1778, c_2244])).
% 5.21/2.04  tff(c_3090, plain, (![B_384]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_384))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_384)) | ~m1_subset_1(B_384, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2248])).
% 5.21/2.04  tff(c_3118, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_3090])).
% 5.21/2.04  tff(c_3131, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_2239, c_3118])).
% 5.21/2.04  tff(c_44, plain, (![A_55, B_57]: (k7_subset_1(u1_struct_0(A_55), k2_pre_topc(A_55, B_57), k1_tops_1(A_55, B_57))=k2_tops_1(A_55, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.21/2.04  tff(c_3138, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3131, c_44])).
% 5.21/2.04  tff(c_3145, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1538, c_3138])).
% 5.21/2.04  tff(c_3147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1539, c_3145])).
% 5.21/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/2.04  
% 5.21/2.04  Inference rules
% 5.21/2.04  ----------------------
% 5.21/2.04  #Ref     : 0
% 5.21/2.04  #Sup     : 739
% 5.21/2.04  #Fact    : 0
% 5.21/2.04  #Define  : 0
% 5.21/2.04  #Split   : 11
% 5.21/2.04  #Chain   : 0
% 5.21/2.04  #Close   : 0
% 5.21/2.04  
% 5.21/2.04  Ordering : KBO
% 5.21/2.04  
% 5.21/2.04  Simplification rules
% 5.21/2.04  ----------------------
% 5.21/2.04  #Subsume      : 13
% 5.21/2.04  #Demod        : 405
% 5.21/2.04  #Tautology    : 376
% 5.21/2.04  #SimpNegUnit  : 2
% 5.21/2.04  #BackRed      : 6
% 5.21/2.04  
% 5.21/2.04  #Partial instantiations: 0
% 5.21/2.04  #Strategies tried      : 1
% 5.21/2.04  
% 5.21/2.04  Timing (in seconds)
% 5.21/2.04  ----------------------
% 5.21/2.05  Preprocessing        : 0.36
% 5.21/2.05  Parsing              : 0.19
% 5.21/2.05  CNF conversion       : 0.02
% 5.21/2.05  Main loop            : 0.93
% 5.21/2.05  Inferencing          : 0.32
% 5.21/2.05  Reduction            : 0.34
% 5.21/2.05  Demodulation         : 0.26
% 5.21/2.05  BG Simplification    : 0.04
% 5.21/2.05  Subsumption          : 0.16
% 5.21/2.05  Abstraction          : 0.05
% 5.21/2.05  MUC search           : 0.00
% 5.21/2.05  Cooper               : 0.00
% 5.21/2.05  Total                : 1.33
% 5.21/2.05  Index Insertion      : 0.00
% 5.21/2.05  Index Deletion       : 0.00
% 5.21/2.05  Index Matching       : 0.00
% 5.21/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
