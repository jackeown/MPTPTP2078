%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:01 EST 2020

% Result     : Theorem 5.72s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 750 expanded)
%              Number of leaves         :   50 ( 280 expanded)
%              Depth                    :   13
%              Number of atoms          :  235 (1536 expanded)
%              Number of equality atoms :   57 ( 425 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_175,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_163,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_152,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_subset_1(u1_struct_0(A),k2_struct_0(A),k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
             => k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_pre_topc)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_84,plain,
    ( k2_tops_1('#skF_3','#skF_4') != '#skF_4'
    | ~ v3_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_115,plain,(
    ~ v3_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_82,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_56,plain,(
    ! [A_37] :
      ( l1_struct_0(A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_116,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_154,plain,(
    ! [A_69] :
      ( u1_struct_0(A_69) = k2_struct_0(A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_56,c_116])).

tff(c_158,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_154])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_159,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_80])).

tff(c_507,plain,(
    ! [A_124,B_125] :
      ( k1_tops_1(A_124,B_125) = k1_xboole_0
      | ~ v2_tops_1(B_125,A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_514,plain,(
    ! [B_125] :
      ( k1_tops_1('#skF_3',B_125) = k1_xboole_0
      | ~ v2_tops_1(B_125,'#skF_3')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_507])).

tff(c_536,plain,(
    ! [B_128] :
      ( k1_tops_1('#skF_3',B_128) = k1_xboole_0
      | ~ v2_tops_1(B_128,'#skF_3')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_514])).

tff(c_553,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_159,c_536])).

tff(c_556,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_553])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_90,plain,
    ( v3_tops_1('#skF_4','#skF_3')
    | k2_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_179,plain,(
    k2_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_90])).

tff(c_717,plain,(
    ! [B_146,A_147] :
      ( v2_tops_1(B_146,A_147)
      | ~ r1_tarski(B_146,k2_tops_1(A_147,B_146))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_723,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_717])).

tff(c_731,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_159,c_158,c_24,c_723])).

tff(c_733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_556,c_731])).

tff(c_735,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_553])).

tff(c_78,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1185,plain,(
    ! [B_192,A_193] :
      ( v3_tops_1(B_192,A_193)
      | ~ v4_pre_topc(B_192,A_193)
      | ~ v2_tops_1(B_192,A_193)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1200,plain,(
    ! [B_192] :
      ( v3_tops_1(B_192,'#skF_3')
      | ~ v4_pre_topc(B_192,'#skF_3')
      | ~ v2_tops_1(B_192,'#skF_3')
      | ~ m1_subset_1(B_192,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_1185])).

tff(c_1255,plain,(
    ! [B_199] :
      ( v3_tops_1(B_199,'#skF_3')
      | ~ v4_pre_topc(B_199,'#skF_3')
      | ~ v2_tops_1(B_199,'#skF_3')
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1200])).

tff(c_1270,plain,
    ( v3_tops_1('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_159,c_1255])).

tff(c_1284,plain,(
    v3_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_78,c_1270])).

tff(c_1286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_1284])).

tff(c_1287,plain,(
    k2_tops_1('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1289,plain,(
    ! [A_200] :
      ( u1_struct_0(A_200) = k2_struct_0(A_200)
      | ~ l1_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1327,plain,(
    ! [A_203] :
      ( u1_struct_0(A_203) = k2_struct_0(A_203)
      | ~ l1_pre_topc(A_203) ) ),
    inference(resolution,[status(thm)],[c_56,c_1289])).

tff(c_1331,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1327])).

tff(c_1347,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1331,c_80])).

tff(c_28,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1570,plain,(
    ! [A_242,B_243,C_244] :
      ( k7_subset_1(A_242,B_243,C_244) = k4_xboole_0(B_243,C_244)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(A_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1580,plain,(
    ! [C_244] : k7_subset_1(k2_struct_0('#skF_3'),'#skF_4',C_244) = k4_xboole_0('#skF_4',C_244) ),
    inference(resolution,[status(thm)],[c_1347,c_1570])).

tff(c_1288,plain,(
    v3_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1611,plain,(
    ! [B_249,A_250] :
      ( v2_tops_1(B_249,A_250)
      | ~ v3_tops_1(B_249,A_250)
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ l1_pre_topc(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1618,plain,(
    ! [B_249] :
      ( v2_tops_1(B_249,'#skF_3')
      | ~ v3_tops_1(B_249,'#skF_3')
      | ~ m1_subset_1(B_249,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_1611])).

tff(c_1656,plain,(
    ! [B_257] :
      ( v2_tops_1(B_257,'#skF_3')
      | ~ v3_tops_1(B_257,'#skF_3')
      | ~ m1_subset_1(B_257,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1618])).

tff(c_1663,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | ~ v3_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1347,c_1656])).

tff(c_1675,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_1663])).

tff(c_1679,plain,(
    ! [A_258,B_259] :
      ( k1_tops_1(A_258,B_259) = k1_xboole_0
      | ~ v2_tops_1(B_259,A_258)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1686,plain,(
    ! [B_259] :
      ( k1_tops_1('#skF_3',B_259) = k1_xboole_0
      | ~ v2_tops_1(B_259,'#skF_3')
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_1679])).

tff(c_1714,plain,(
    ! [B_265] :
      ( k1_tops_1('#skF_3',B_265) = k1_xboole_0
      | ~ v2_tops_1(B_265,'#skF_3')
      | ~ m1_subset_1(B_265,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1686])).

tff(c_1721,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1347,c_1714])).

tff(c_1733,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1675,c_1721])).

tff(c_1493,plain,(
    ! [A_235,B_236] :
      ( k4_xboole_0(A_235,B_236) = k3_subset_1(A_235,B_236)
      | ~ m1_subset_1(B_236,k1_zfmisc_1(A_235)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1507,plain,(
    k4_xboole_0(k2_struct_0('#skF_3'),'#skF_4') = k3_subset_1(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1347,c_1493])).

tff(c_32,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ! [A_17] : m1_subset_1(k2_subset_1(A_17),k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,(
    ! [A_17] : m1_subset_1(A_17,k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_1581,plain,(
    ! [A_17,C_244] : k7_subset_1(A_17,A_17,C_244) = k4_xboole_0(A_17,C_244) ),
    inference(resolution,[status(thm)],[c_91,c_1570])).

tff(c_2669,plain,(
    ! [A_331,B_332] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_331),k2_struct_0(A_331),B_332),A_331)
      | ~ v4_pre_topc(B_332,A_331)
      | ~ m1_subset_1(B_332,k1_zfmisc_1(u1_struct_0(A_331)))
      | ~ l1_pre_topc(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2672,plain,(
    ! [B_332] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'),B_332),'#skF_3')
      | ~ v4_pre_topc(B_332,'#skF_3')
      | ~ m1_subset_1(B_332,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_2669])).

tff(c_2739,plain,(
    ! [B_339] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_3'),B_339),'#skF_3')
      | ~ v4_pre_topc(B_339,'#skF_3')
      | ~ m1_subset_1(B_339,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1331,c_1581,c_2672])).

tff(c_2753,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1507,c_2739])).

tff(c_2761,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_78,c_2753])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k3_subset_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1809,plain,(
    ! [A_271,B_272] :
      ( k4_xboole_0(A_271,k3_subset_1(A_271,B_272)) = k3_subset_1(A_271,k3_subset_1(A_271,B_272))
      | ~ m1_subset_1(B_272,k1_zfmisc_1(A_271)) ) ),
    inference(resolution,[status(thm)],[c_38,c_1493])).

tff(c_1819,plain,(
    k4_xboole_0(k2_struct_0('#skF_3'),k3_subset_1(k2_struct_0('#skF_3'),'#skF_4')) = k3_subset_1(k2_struct_0('#skF_3'),k3_subset_1(k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_1347,c_1809])).

tff(c_2898,plain,(
    ! [A_344,B_345] :
      ( k7_subset_1(u1_struct_0(A_344),k2_struct_0(A_344),k7_subset_1(u1_struct_0(A_344),k2_struct_0(A_344),B_345)) = B_345
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ l1_struct_0(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2919,plain,(
    ! [B_345] :
      ( k7_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'),k7_subset_1(u1_struct_0('#skF_3'),k2_struct_0('#skF_3'),B_345)) = B_345
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_2898])).

tff(c_2927,plain,(
    ! [B_345] :
      ( k4_xboole_0(k2_struct_0('#skF_3'),k4_xboole_0(k2_struct_0('#skF_3'),B_345)) = B_345
      | ~ m1_subset_1(B_345,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1331,c_1581,c_1331,c_1581,c_2919])).

tff(c_2931,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2927])).

tff(c_2934,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2931])).

tff(c_2938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2934])).

tff(c_2946,plain,(
    ! [B_346] :
      ( k4_xboole_0(k2_struct_0('#skF_3'),k4_xboole_0(k2_struct_0('#skF_3'),B_346)) = B_346
      | ~ m1_subset_1(B_346,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_2927])).

tff(c_2978,plain,
    ( k4_xboole_0(k2_struct_0('#skF_3'),k3_subset_1(k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1507,c_2946])).

tff(c_2992,plain,(
    k3_subset_1(k2_struct_0('#skF_3'),k3_subset_1(k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_1819,c_2978])).

tff(c_3043,plain,(
    k4_xboole_0(k2_struct_0('#skF_3'),k3_subset_1(k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2992,c_1819])).

tff(c_2742,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_3'),k3_subset_1(k2_struct_0('#skF_3'),'#skF_4')),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1819,c_2739])).

tff(c_2764,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2742])).

tff(c_2768,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_38,c_2764])).

tff(c_2772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_2768])).

tff(c_2774,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2742])).

tff(c_4187,plain,(
    ! [A_395,B_396] :
      ( k2_pre_topc(A_395,k7_subset_1(u1_struct_0(A_395),k2_struct_0(A_395),B_396)) = k7_subset_1(u1_struct_0(A_395),k2_struct_0(A_395),B_396)
      | ~ v3_pre_topc(B_396,A_395)
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0(A_395)))
      | ~ l1_pre_topc(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4206,plain,(
    ! [B_396] :
      ( k2_pre_topc('#skF_3',k7_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'),B_396)) = k7_subset_1(u1_struct_0('#skF_3'),k2_struct_0('#skF_3'),B_396)
      | ~ v3_pre_topc(B_396,'#skF_3')
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_4187])).

tff(c_4331,plain,(
    ! [B_400] :
      ( k2_pre_topc('#skF_3',k4_xboole_0(k2_struct_0('#skF_3'),B_400)) = k4_xboole_0(k2_struct_0('#skF_3'),B_400)
      | ~ v3_pre_topc(B_400,'#skF_3')
      | ~ m1_subset_1(B_400,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1331,c_1581,c_1331,c_1581,c_4206])).

tff(c_4370,plain,
    ( k2_pre_topc('#skF_3',k4_xboole_0(k2_struct_0('#skF_3'),k3_subset_1(k2_struct_0('#skF_3'),'#skF_4'))) = k4_xboole_0(k2_struct_0('#skF_3'),k3_subset_1(k2_struct_0('#skF_3'),'#skF_4'))
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2774,c_4331])).

tff(c_4421,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2761,c_3043,c_3043,c_4370])).

tff(c_3024,plain,(
    ! [A_347,B_348] :
      ( k7_subset_1(u1_struct_0(A_347),k2_pre_topc(A_347,B_348),k1_tops_1(A_347,B_348)) = k2_tops_1(A_347,B_348)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0(A_347)))
      | ~ l1_pre_topc(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3036,plain,(
    ! [B_348] :
      ( k7_subset_1(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',B_348),k1_tops_1('#skF_3',B_348)) = k2_tops_1('#skF_3',B_348)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_3024])).

tff(c_3042,plain,(
    ! [B_348] :
      ( k7_subset_1(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',B_348),k1_tops_1('#skF_3',B_348)) = k2_tops_1('#skF_3',B_348)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1331,c_3036])).

tff(c_4439,plain,
    ( k7_subset_1(k2_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4421,c_3042])).

tff(c_4446,plain,(
    k2_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_28,c_1580,c_1733,c_4439])).

tff(c_4448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1287,c_4446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:10:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.72/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.72/2.09  
% 5.72/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.72/2.09  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 5.72/2.09  
% 5.72/2.09  %Foreground sorts:
% 5.72/2.09  
% 5.72/2.09  
% 5.72/2.09  %Background operators:
% 5.72/2.09  
% 5.72/2.09  
% 5.72/2.09  %Foreground operators:
% 5.72/2.09  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.72/2.09  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.72/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.72/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.72/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.72/2.09  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.72/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.72/2.09  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.72/2.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.72/2.09  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 5.72/2.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.72/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.72/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.72/2.09  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.72/2.09  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.72/2.09  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.72/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.72/2.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.72/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.72/2.09  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.72/2.09  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.72/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.72/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.72/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.72/2.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.72/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.72/2.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.72/2.09  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.72/2.09  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.72/2.09  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.72/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.72/2.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.72/2.09  
% 5.97/2.12  tff(f_175, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 5.97/2.12  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.97/2.12  tff(f_83, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.97/2.12  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 5.97/2.12  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.97/2.12  tff(f_143, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 5.97/2.12  tff(f_163, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 5.97/2.12  tff(f_44, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.97/2.12  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.97/2.12  tff(f_152, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 5.97/2.12  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.97/2.12  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.97/2.12  tff(f_54, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.97/2.12  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 5.97/2.12  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.97/2.12  tff(f_103, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_subset_1(u1_struct_0(A), k2_struct_0(A), k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 5.97/2.12  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) => (k2_pre_topc(A, k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))) & ((v2_pre_topc(A) & (k2_pre_topc(A, k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_pre_topc)).
% 5.97/2.12  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.97/2.12  tff(c_84, plain, (k2_tops_1('#skF_3', '#skF_4')!='#skF_4' | ~v3_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.97/2.12  tff(c_115, plain, (~v3_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_84])).
% 5.97/2.12  tff(c_82, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.97/2.12  tff(c_56, plain, (![A_37]: (l1_struct_0(A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.97/2.12  tff(c_116, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.97/2.12  tff(c_154, plain, (![A_69]: (u1_struct_0(A_69)=k2_struct_0(A_69) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_56, c_116])).
% 5.97/2.12  tff(c_158, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_154])).
% 5.97/2.12  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.97/2.12  tff(c_159, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_80])).
% 5.97/2.12  tff(c_507, plain, (![A_124, B_125]: (k1_tops_1(A_124, B_125)=k1_xboole_0 | ~v2_tops_1(B_125, A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.97/2.12  tff(c_514, plain, (![B_125]: (k1_tops_1('#skF_3', B_125)=k1_xboole_0 | ~v2_tops_1(B_125, '#skF_3') | ~m1_subset_1(B_125, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_507])).
% 5.97/2.12  tff(c_536, plain, (![B_128]: (k1_tops_1('#skF_3', B_128)=k1_xboole_0 | ~v2_tops_1(B_128, '#skF_3') | ~m1_subset_1(B_128, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_514])).
% 5.97/2.12  tff(c_553, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_159, c_536])).
% 5.97/2.12  tff(c_556, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_553])).
% 5.97/2.12  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.97/2.12  tff(c_90, plain, (v3_tops_1('#skF_4', '#skF_3') | k2_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.97/2.12  tff(c_179, plain, (k2_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_115, c_90])).
% 5.97/2.12  tff(c_717, plain, (![B_146, A_147]: (v2_tops_1(B_146, A_147) | ~r1_tarski(B_146, k2_tops_1(A_147, B_146)) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.97/2.12  tff(c_723, plain, (v2_tops_1('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_179, c_717])).
% 5.97/2.12  tff(c_731, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_159, c_158, c_24, c_723])).
% 5.97/2.12  tff(c_733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_556, c_731])).
% 5.97/2.12  tff(c_735, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_553])).
% 5.97/2.12  tff(c_78, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.97/2.12  tff(c_1185, plain, (![B_192, A_193]: (v3_tops_1(B_192, A_193) | ~v4_pre_topc(B_192, A_193) | ~v2_tops_1(B_192, A_193) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.97/2.12  tff(c_1200, plain, (![B_192]: (v3_tops_1(B_192, '#skF_3') | ~v4_pre_topc(B_192, '#skF_3') | ~v2_tops_1(B_192, '#skF_3') | ~m1_subset_1(B_192, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_1185])).
% 5.97/2.12  tff(c_1255, plain, (![B_199]: (v3_tops_1(B_199, '#skF_3') | ~v4_pre_topc(B_199, '#skF_3') | ~v2_tops_1(B_199, '#skF_3') | ~m1_subset_1(B_199, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1200])).
% 5.97/2.12  tff(c_1270, plain, (v3_tops_1('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_159, c_1255])).
% 5.97/2.12  tff(c_1284, plain, (v3_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_735, c_78, c_1270])).
% 5.97/2.12  tff(c_1286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_1284])).
% 5.97/2.12  tff(c_1287, plain, (k2_tops_1('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_84])).
% 5.97/2.12  tff(c_1289, plain, (![A_200]: (u1_struct_0(A_200)=k2_struct_0(A_200) | ~l1_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.97/2.12  tff(c_1327, plain, (![A_203]: (u1_struct_0(A_203)=k2_struct_0(A_203) | ~l1_pre_topc(A_203))), inference(resolution, [status(thm)], [c_56, c_1289])).
% 5.97/2.12  tff(c_1331, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1327])).
% 5.97/2.12  tff(c_1347, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1331, c_80])).
% 5.97/2.12  tff(c_28, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.97/2.12  tff(c_1570, plain, (![A_242, B_243, C_244]: (k7_subset_1(A_242, B_243, C_244)=k4_xboole_0(B_243, C_244) | ~m1_subset_1(B_243, k1_zfmisc_1(A_242)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.97/2.12  tff(c_1580, plain, (![C_244]: (k7_subset_1(k2_struct_0('#skF_3'), '#skF_4', C_244)=k4_xboole_0('#skF_4', C_244))), inference(resolution, [status(thm)], [c_1347, c_1570])).
% 5.97/2.12  tff(c_1288, plain, (v3_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_84])).
% 5.97/2.12  tff(c_1611, plain, (![B_249, A_250]: (v2_tops_1(B_249, A_250) | ~v3_tops_1(B_249, A_250) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(A_250))) | ~l1_pre_topc(A_250))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.97/2.12  tff(c_1618, plain, (![B_249]: (v2_tops_1(B_249, '#skF_3') | ~v3_tops_1(B_249, '#skF_3') | ~m1_subset_1(B_249, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1331, c_1611])).
% 5.97/2.12  tff(c_1656, plain, (![B_257]: (v2_tops_1(B_257, '#skF_3') | ~v3_tops_1(B_257, '#skF_3') | ~m1_subset_1(B_257, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1618])).
% 5.97/2.12  tff(c_1663, plain, (v2_tops_1('#skF_4', '#skF_3') | ~v3_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1347, c_1656])).
% 5.97/2.12  tff(c_1675, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1288, c_1663])).
% 5.97/2.12  tff(c_1679, plain, (![A_258, B_259]: (k1_tops_1(A_258, B_259)=k1_xboole_0 | ~v2_tops_1(B_259, A_258) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.97/2.12  tff(c_1686, plain, (![B_259]: (k1_tops_1('#skF_3', B_259)=k1_xboole_0 | ~v2_tops_1(B_259, '#skF_3') | ~m1_subset_1(B_259, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1331, c_1679])).
% 5.97/2.12  tff(c_1714, plain, (![B_265]: (k1_tops_1('#skF_3', B_265)=k1_xboole_0 | ~v2_tops_1(B_265, '#skF_3') | ~m1_subset_1(B_265, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1686])).
% 5.97/2.12  tff(c_1721, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1347, c_1714])).
% 5.97/2.12  tff(c_1733, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1675, c_1721])).
% 5.97/2.12  tff(c_1493, plain, (![A_235, B_236]: (k4_xboole_0(A_235, B_236)=k3_subset_1(A_235, B_236) | ~m1_subset_1(B_236, k1_zfmisc_1(A_235)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.97/2.12  tff(c_1507, plain, (k4_xboole_0(k2_struct_0('#skF_3'), '#skF_4')=k3_subset_1(k2_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_1347, c_1493])).
% 5.97/2.12  tff(c_32, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.97/2.12  tff(c_36, plain, (![A_17]: (m1_subset_1(k2_subset_1(A_17), k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.97/2.12  tff(c_91, plain, (![A_17]: (m1_subset_1(A_17, k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 5.97/2.12  tff(c_1581, plain, (![A_17, C_244]: (k7_subset_1(A_17, A_17, C_244)=k4_xboole_0(A_17, C_244))), inference(resolution, [status(thm)], [c_91, c_1570])).
% 5.97/2.12  tff(c_2669, plain, (![A_331, B_332]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_331), k2_struct_0(A_331), B_332), A_331) | ~v4_pre_topc(B_332, A_331) | ~m1_subset_1(B_332, k1_zfmisc_1(u1_struct_0(A_331))) | ~l1_pre_topc(A_331))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.97/2.12  tff(c_2672, plain, (![B_332]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_3'), B_332), '#skF_3') | ~v4_pre_topc(B_332, '#skF_3') | ~m1_subset_1(B_332, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1331, c_2669])).
% 5.97/2.12  tff(c_2739, plain, (![B_339]: (v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_3'), B_339), '#skF_3') | ~v4_pre_topc(B_339, '#skF_3') | ~m1_subset_1(B_339, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1331, c_1581, c_2672])).
% 5.97/2.12  tff(c_2753, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1507, c_2739])).
% 5.97/2.12  tff(c_2761, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_78, c_2753])).
% 5.97/2.12  tff(c_38, plain, (![A_18, B_19]: (m1_subset_1(k3_subset_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.97/2.12  tff(c_1809, plain, (![A_271, B_272]: (k4_xboole_0(A_271, k3_subset_1(A_271, B_272))=k3_subset_1(A_271, k3_subset_1(A_271, B_272)) | ~m1_subset_1(B_272, k1_zfmisc_1(A_271)))), inference(resolution, [status(thm)], [c_38, c_1493])).
% 5.97/2.12  tff(c_1819, plain, (k4_xboole_0(k2_struct_0('#skF_3'), k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'))=k3_subset_1(k2_struct_0('#skF_3'), k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_1347, c_1809])).
% 5.97/2.12  tff(c_2898, plain, (![A_344, B_345]: (k7_subset_1(u1_struct_0(A_344), k2_struct_0(A_344), k7_subset_1(u1_struct_0(A_344), k2_struct_0(A_344), B_345))=B_345 | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_344))) | ~l1_struct_0(A_344))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.97/2.12  tff(c_2919, plain, (![B_345]: (k7_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_3'), k7_subset_1(u1_struct_0('#skF_3'), k2_struct_0('#skF_3'), B_345))=B_345 | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1331, c_2898])).
% 5.97/2.12  tff(c_2927, plain, (![B_345]: (k4_xboole_0(k2_struct_0('#skF_3'), k4_xboole_0(k2_struct_0('#skF_3'), B_345))=B_345 | ~m1_subset_1(B_345, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1331, c_1581, c_1331, c_1581, c_2919])).
% 5.97/2.12  tff(c_2931, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_2927])).
% 5.97/2.12  tff(c_2934, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2931])).
% 5.97/2.12  tff(c_2938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_2934])).
% 5.97/2.12  tff(c_2946, plain, (![B_346]: (k4_xboole_0(k2_struct_0('#skF_3'), k4_xboole_0(k2_struct_0('#skF_3'), B_346))=B_346 | ~m1_subset_1(B_346, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_2927])).
% 5.97/2.12  tff(c_2978, plain, (k4_xboole_0(k2_struct_0('#skF_3'), k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1507, c_2946])).
% 5.97/2.12  tff(c_2992, plain, (k3_subset_1(k2_struct_0('#skF_3'), k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_1819, c_2978])).
% 5.97/2.12  tff(c_3043, plain, (k4_xboole_0(k2_struct_0('#skF_3'), k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2992, c_1819])).
% 5.97/2.12  tff(c_2742, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_3'), k3_subset_1(k2_struct_0('#skF_3'), '#skF_4')), '#skF_3') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1819, c_2739])).
% 5.97/2.12  tff(c_2764, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_2742])).
% 5.97/2.12  tff(c_2768, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_38, c_2764])).
% 5.97/2.12  tff(c_2772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1347, c_2768])).
% 5.97/2.12  tff(c_2774, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_2742])).
% 5.97/2.12  tff(c_4187, plain, (![A_395, B_396]: (k2_pre_topc(A_395, k7_subset_1(u1_struct_0(A_395), k2_struct_0(A_395), B_396))=k7_subset_1(u1_struct_0(A_395), k2_struct_0(A_395), B_396) | ~v3_pre_topc(B_396, A_395) | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0(A_395))) | ~l1_pre_topc(A_395))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.97/2.12  tff(c_4206, plain, (![B_396]: (k2_pre_topc('#skF_3', k7_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_3'), B_396))=k7_subset_1(u1_struct_0('#skF_3'), k2_struct_0('#skF_3'), B_396) | ~v3_pre_topc(B_396, '#skF_3') | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1331, c_4187])).
% 5.97/2.12  tff(c_4331, plain, (![B_400]: (k2_pre_topc('#skF_3', k4_xboole_0(k2_struct_0('#skF_3'), B_400))=k4_xboole_0(k2_struct_0('#skF_3'), B_400) | ~v3_pre_topc(B_400, '#skF_3') | ~m1_subset_1(B_400, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1331, c_1581, c_1331, c_1581, c_4206])).
% 5.97/2.12  tff(c_4370, plain, (k2_pre_topc('#skF_3', k4_xboole_0(k2_struct_0('#skF_3'), k3_subset_1(k2_struct_0('#skF_3'), '#skF_4')))=k4_xboole_0(k2_struct_0('#skF_3'), k3_subset_1(k2_struct_0('#skF_3'), '#skF_4')) | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_2774, c_4331])).
% 5.97/2.12  tff(c_4421, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2761, c_3043, c_3043, c_4370])).
% 5.97/2.12  tff(c_3024, plain, (![A_347, B_348]: (k7_subset_1(u1_struct_0(A_347), k2_pre_topc(A_347, B_348), k1_tops_1(A_347, B_348))=k2_tops_1(A_347, B_348) | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0(A_347))) | ~l1_pre_topc(A_347))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.97/2.12  tff(c_3036, plain, (![B_348]: (k7_subset_1(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', B_348), k1_tops_1('#skF_3', B_348))=k2_tops_1('#skF_3', B_348) | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1331, c_3024])).
% 5.97/2.12  tff(c_3042, plain, (![B_348]: (k7_subset_1(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', B_348), k1_tops_1('#skF_3', B_348))=k2_tops_1('#skF_3', B_348) | ~m1_subset_1(B_348, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1331, c_3036])).
% 5.97/2.12  tff(c_4439, plain, (k7_subset_1(k2_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4421, c_3042])).
% 5.97/2.12  tff(c_4446, plain, (k2_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_28, c_1580, c_1733, c_4439])).
% 5.97/2.12  tff(c_4448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1287, c_4446])).
% 5.97/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.12  
% 5.97/2.12  Inference rules
% 5.97/2.12  ----------------------
% 5.97/2.12  #Ref     : 0
% 5.97/2.12  #Sup     : 941
% 5.97/2.12  #Fact    : 0
% 5.97/2.12  #Define  : 0
% 5.97/2.12  #Split   : 19
% 5.97/2.12  #Chain   : 0
% 5.97/2.12  #Close   : 0
% 5.97/2.12  
% 5.97/2.12  Ordering : KBO
% 5.97/2.12  
% 5.97/2.12  Simplification rules
% 5.97/2.12  ----------------------
% 5.97/2.12  #Subsume      : 82
% 5.97/2.12  #Demod        : 287
% 5.97/2.12  #Tautology    : 238
% 5.97/2.12  #SimpNegUnit  : 29
% 5.97/2.12  #BackRed      : 5
% 5.97/2.12  
% 5.97/2.12  #Partial instantiations: 0
% 5.97/2.12  #Strategies tried      : 1
% 5.97/2.12  
% 5.97/2.12  Timing (in seconds)
% 5.97/2.12  ----------------------
% 5.97/2.12  Preprocessing        : 0.37
% 5.97/2.12  Parsing              : 0.19
% 5.97/2.12  CNF conversion       : 0.03
% 5.97/2.12  Main loop            : 0.97
% 5.97/2.12  Inferencing          : 0.31
% 5.97/2.12  Reduction            : 0.32
% 5.97/2.12  Demodulation         : 0.23
% 5.97/2.12  BG Simplification    : 0.05
% 5.97/2.12  Subsumption          : 0.22
% 5.97/2.12  Abstraction          : 0.06
% 5.97/2.12  MUC search           : 0.00
% 5.97/2.12  Cooper               : 0.00
% 5.97/2.12  Total                : 1.39
% 5.97/2.12  Index Insertion      : 0.00
% 5.97/2.12  Index Deletion       : 0.00
% 5.97/2.12  Index Matching       : 0.00
% 5.97/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
