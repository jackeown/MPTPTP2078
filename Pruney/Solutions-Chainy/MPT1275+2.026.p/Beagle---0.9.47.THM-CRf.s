%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:05 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 217 expanded)
%              Number of leaves         :   35 (  93 expanded)
%              Depth                    :    9
%              Number of atoms          :  167 ( 539 expanded)
%              Number of equality atoms :   39 ( 116 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_70,axiom,(
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

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_54,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_59,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_78,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_48])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_388,plain,(
    ! [B_82,A_83] :
      ( v2_tops_1(B_82,A_83)
      | k1_tops_1(A_83,B_82) != k1_xboole_0
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_399,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_388])).

tff(c_408,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_399])).

tff(c_410,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_408])).

tff(c_470,plain,(
    ! [A_93,B_94] :
      ( k1_tops_1(A_93,B_94) = k1_xboole_0
      | ~ v2_tops_1(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_481,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_470])).

tff(c_490,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_481])).

tff(c_491,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_490])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_809,plain,(
    ! [B_125,A_126] :
      ( v2_tops_1(B_125,A_126)
      | ~ r1_tarski(B_125,k2_tops_1(A_126,B_125))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_816,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_809])).

tff(c_822,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_6,c_816])).

tff(c_824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_822])).

tff(c_825,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_408])).

tff(c_42,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_831,plain,(
    ! [A_127,B_128] :
      ( k2_pre_topc(A_127,B_128) = B_128
      | ~ v4_pre_topc(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_842,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_831])).

tff(c_851,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_842])).

tff(c_918,plain,(
    ! [B_140,A_141] :
      ( v3_tops_1(B_140,A_141)
      | ~ v2_tops_1(k2_pre_topc(A_141,B_140),A_141)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_920,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_918])).

tff(c_922,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_825,c_920])).

tff(c_924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_922])).

tff(c_926,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_925,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1181,plain,(
    ! [B_180,A_181] :
      ( v2_tops_1(B_180,A_181)
      | ~ v3_tops_1(B_180,A_181)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1192,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1181])).

tff(c_1201,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_925,c_1192])).

tff(c_1655,plain,(
    ! [B_228,A_229] :
      ( r1_tarski(B_228,k2_tops_1(A_229,B_228))
      | ~ v2_tops_1(B_228,A_229)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1663,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1655])).

tff(c_1671,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1201,c_1663])).

tff(c_1000,plain,(
    ! [A_153,B_154] :
      ( k4_xboole_0(A_153,B_154) = k3_subset_1(A_153,B_154)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1016,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = k3_subset_1(A_10,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_1000])).

tff(c_1115,plain,(
    ! [A_166,B_167,C_168] :
      ( k7_subset_1(A_166,B_167,C_168) = k4_xboole_0(B_167,C_168)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1126,plain,(
    ! [C_168] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_168) = k4_xboole_0('#skF_2',C_168) ),
    inference(resolution,[status(thm)],[c_44,c_1115])).

tff(c_1305,plain,(
    ! [A_193,B_194] :
      ( k2_pre_topc(A_193,B_194) = B_194
      | ~ v4_pre_topc(B_194,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1316,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1305])).

tff(c_1325,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_1316])).

tff(c_1333,plain,(
    ! [A_197,B_198] :
      ( k1_tops_1(A_197,B_198) = k1_xboole_0
      | ~ v2_tops_1(B_198,A_197)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1344,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1333])).

tff(c_1353,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1201,c_1344])).

tff(c_1726,plain,(
    ! [A_233,B_234] :
      ( k7_subset_1(u1_struct_0(A_233),k2_pre_topc(A_233,B_234),k1_tops_1(A_233,B_234)) = k2_tops_1(A_233,B_234)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1738,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1353,c_1726])).

tff(c_1747,plain,(
    k3_subset_1('#skF_2',k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1016,c_1126,c_1325,c_1738])).

tff(c_970,plain,(
    ! [A_148,B_149] :
      ( m1_subset_1(k3_subset_1(A_148,B_149),k1_zfmisc_1(A_148))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_975,plain,(
    ! [A_150,B_151] :
      ( r1_tarski(k3_subset_1(A_150,B_151),A_150)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(A_150)) ) ),
    inference(resolution,[status(thm)],[c_970,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_983,plain,(
    ! [A_150,B_151] :
      ( k3_subset_1(A_150,B_151) = A_150
      | ~ r1_tarski(A_150,k3_subset_1(A_150,B_151))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(A_150)) ) ),
    inference(resolution,[status(thm)],[c_975,c_2])).

tff(c_1759,plain,
    ( k3_subset_1('#skF_2',k1_xboole_0) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1747,c_983])).

tff(c_1775,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1671,c_1747,c_1759])).

tff(c_1777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_926,c_1775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.55  
% 3.58/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.56  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.58/1.56  
% 3.58/1.56  %Foreground sorts:
% 3.58/1.56  
% 3.58/1.56  
% 3.58/1.56  %Background operators:
% 3.58/1.56  
% 3.58/1.56  
% 3.58/1.56  %Foreground operators:
% 3.58/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.58/1.56  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.58/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.56  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.58/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.58/1.56  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.58/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.56  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.58/1.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.58/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.56  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.58/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.56  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.58/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.58/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.58/1.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.58/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.56  
% 3.58/1.57  tff(f_125, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 3.58/1.57  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.58/1.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.58/1.57  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 3.58/1.57  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.58/1.57  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 3.58/1.57  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.58/1.57  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 3.58/1.57  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.58/1.57  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.58/1.57  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.58/1.57  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.58/1.57  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.58/1.57  tff(c_54, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.57  tff(c_59, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_54])).
% 3.58/1.57  tff(c_48, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.57  tff(c_78, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_48])).
% 3.58/1.57  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.57  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.57  tff(c_388, plain, (![B_82, A_83]: (v2_tops_1(B_82, A_83) | k1_tops_1(A_83, B_82)!=k1_xboole_0 | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.58/1.57  tff(c_399, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_388])).
% 3.58/1.57  tff(c_408, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_399])).
% 3.58/1.57  tff(c_410, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_408])).
% 3.58/1.57  tff(c_470, plain, (![A_93, B_94]: (k1_tops_1(A_93, B_94)=k1_xboole_0 | ~v2_tops_1(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.58/1.57  tff(c_481, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_470])).
% 3.58/1.57  tff(c_490, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_481])).
% 3.58/1.57  tff(c_491, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_410, c_490])).
% 3.58/1.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.57  tff(c_809, plain, (![B_125, A_126]: (v2_tops_1(B_125, A_126) | ~r1_tarski(B_125, k2_tops_1(A_126, B_125)) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.58/1.57  tff(c_816, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_59, c_809])).
% 3.58/1.57  tff(c_822, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_6, c_816])).
% 3.58/1.57  tff(c_824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_491, c_822])).
% 3.58/1.57  tff(c_825, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_408])).
% 3.58/1.57  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.57  tff(c_831, plain, (![A_127, B_128]: (k2_pre_topc(A_127, B_128)=B_128 | ~v4_pre_topc(B_128, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.58/1.57  tff(c_842, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_831])).
% 3.58/1.57  tff(c_851, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_842])).
% 3.58/1.57  tff(c_918, plain, (![B_140, A_141]: (v3_tops_1(B_140, A_141) | ~v2_tops_1(k2_pre_topc(A_141, B_140), A_141) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.58/1.57  tff(c_920, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_851, c_918])).
% 3.58/1.57  tff(c_922, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_825, c_920])).
% 3.58/1.57  tff(c_924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_922])).
% 3.58/1.57  tff(c_926, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 3.58/1.57  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.58/1.57  tff(c_925, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 3.58/1.57  tff(c_1181, plain, (![B_180, A_181]: (v2_tops_1(B_180, A_181) | ~v3_tops_1(B_180, A_181) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.58/1.57  tff(c_1192, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1181])).
% 3.58/1.57  tff(c_1201, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_925, c_1192])).
% 3.58/1.57  tff(c_1655, plain, (![B_228, A_229]: (r1_tarski(B_228, k2_tops_1(A_229, B_228)) | ~v2_tops_1(B_228, A_229) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_pre_topc(A_229))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.58/1.57  tff(c_1663, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1655])).
% 3.58/1.57  tff(c_1671, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1201, c_1663])).
% 3.58/1.57  tff(c_1000, plain, (![A_153, B_154]: (k4_xboole_0(A_153, B_154)=k3_subset_1(A_153, B_154) | ~m1_subset_1(B_154, k1_zfmisc_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.58/1.57  tff(c_1016, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=k3_subset_1(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_1000])).
% 3.58/1.57  tff(c_1115, plain, (![A_166, B_167, C_168]: (k7_subset_1(A_166, B_167, C_168)=k4_xboole_0(B_167, C_168) | ~m1_subset_1(B_167, k1_zfmisc_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.58/1.57  tff(c_1126, plain, (![C_168]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_168)=k4_xboole_0('#skF_2', C_168))), inference(resolution, [status(thm)], [c_44, c_1115])).
% 3.58/1.57  tff(c_1305, plain, (![A_193, B_194]: (k2_pre_topc(A_193, B_194)=B_194 | ~v4_pre_topc(B_194, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.58/1.57  tff(c_1316, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1305])).
% 3.58/1.57  tff(c_1325, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_1316])).
% 3.58/1.57  tff(c_1333, plain, (![A_197, B_198]: (k1_tops_1(A_197, B_198)=k1_xboole_0 | ~v2_tops_1(B_198, A_197) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.58/1.57  tff(c_1344, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1333])).
% 3.58/1.57  tff(c_1353, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1201, c_1344])).
% 3.58/1.57  tff(c_1726, plain, (![A_233, B_234]: (k7_subset_1(u1_struct_0(A_233), k2_pre_topc(A_233, B_234), k1_tops_1(A_233, B_234))=k2_tops_1(A_233, B_234) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.58/1.57  tff(c_1738, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1353, c_1726])).
% 3.58/1.57  tff(c_1747, plain, (k3_subset_1('#skF_2', k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1016, c_1126, c_1325, c_1738])).
% 3.58/1.57  tff(c_970, plain, (![A_148, B_149]: (m1_subset_1(k3_subset_1(A_148, B_149), k1_zfmisc_1(A_148)) | ~m1_subset_1(B_149, k1_zfmisc_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.58/1.57  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.58/1.57  tff(c_975, plain, (![A_150, B_151]: (r1_tarski(k3_subset_1(A_150, B_151), A_150) | ~m1_subset_1(B_151, k1_zfmisc_1(A_150)))), inference(resolution, [status(thm)], [c_970, c_16])).
% 3.58/1.57  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.57  tff(c_983, plain, (![A_150, B_151]: (k3_subset_1(A_150, B_151)=A_150 | ~r1_tarski(A_150, k3_subset_1(A_150, B_151)) | ~m1_subset_1(B_151, k1_zfmisc_1(A_150)))), inference(resolution, [status(thm)], [c_975, c_2])).
% 3.58/1.57  tff(c_1759, plain, (k3_subset_1('#skF_2', k1_xboole_0)='#skF_2' | ~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1747, c_983])).
% 3.58/1.57  tff(c_1775, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1671, c_1747, c_1759])).
% 3.58/1.57  tff(c_1777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_926, c_1775])).
% 3.58/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.57  
% 3.58/1.57  Inference rules
% 3.58/1.57  ----------------------
% 3.58/1.57  #Ref     : 0
% 3.58/1.57  #Sup     : 369
% 3.58/1.57  #Fact    : 0
% 3.58/1.57  #Define  : 0
% 3.58/1.57  #Split   : 4
% 3.58/1.57  #Chain   : 0
% 3.58/1.57  #Close   : 0
% 3.58/1.57  
% 3.58/1.57  Ordering : KBO
% 3.58/1.57  
% 3.58/1.57  Simplification rules
% 3.58/1.57  ----------------------
% 3.58/1.57  #Subsume      : 46
% 3.58/1.57  #Demod        : 226
% 3.58/1.57  #Tautology    : 178
% 3.58/1.57  #SimpNegUnit  : 10
% 3.58/1.57  #BackRed      : 0
% 3.58/1.57  
% 3.58/1.57  #Partial instantiations: 0
% 3.58/1.57  #Strategies tried      : 1
% 3.58/1.57  
% 3.58/1.57  Timing (in seconds)
% 3.58/1.57  ----------------------
% 3.58/1.58  Preprocessing        : 0.33
% 3.58/1.58  Parsing              : 0.18
% 3.58/1.58  CNF conversion       : 0.02
% 3.58/1.58  Main loop            : 0.48
% 3.58/1.58  Inferencing          : 0.18
% 3.58/1.58  Reduction            : 0.15
% 3.58/1.58  Demodulation         : 0.11
% 3.58/1.58  BG Simplification    : 0.03
% 3.58/1.58  Subsumption          : 0.09
% 3.58/1.58  Abstraction          : 0.03
% 3.58/1.58  MUC search           : 0.00
% 3.58/1.58  Cooper               : 0.00
% 3.58/1.58  Total                : 0.85
% 3.58/1.58  Index Insertion      : 0.00
% 3.58/1.58  Index Deletion       : 0.00
% 3.58/1.58  Index Matching       : 0.00
% 3.58/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
