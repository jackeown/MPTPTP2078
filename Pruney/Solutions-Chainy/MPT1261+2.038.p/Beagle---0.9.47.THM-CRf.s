%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:17 EST 2020

% Result     : Theorem 5.00s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 615 expanded)
%              Number of leaves         :   42 ( 220 expanded)
%              Depth                    :   16
%              Number of atoms          :  188 (1208 expanded)
%              Number of equality atoms :   77 ( 369 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3070,plain,(
    ! [A_217,B_218] :
      ( r1_tarski(k1_tops_1(A_217,B_218),B_218)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3078,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_3070])).

tff(c_3083,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3078])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2687,plain,(
    ! [A_192,B_193] :
      ( k4_xboole_0(A_192,B_193) = k3_subset_1(A_192,B_193)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(A_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2694,plain,(
    ! [B_25,A_24] :
      ( k4_xboole_0(B_25,A_24) = k3_subset_1(B_25,A_24)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_2687])).

tff(c_3090,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3083,c_2694])).

tff(c_2794,plain,(
    ! [A_202,B_203,C_204] :
      ( k7_subset_1(A_202,B_203,C_204) = k4_xboole_0(B_203,C_204)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(A_202)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2803,plain,(
    ! [C_204] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_204) = k4_xboole_0('#skF_2',C_204) ),
    inference(resolution,[status(thm)],[c_42,c_2794])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_133,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_267,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1324,plain,(
    ! [B_132,A_133] :
      ( v4_pre_topc(B_132,A_133)
      | k2_pre_topc(A_133,B_132) != B_132
      | ~ v2_pre_topc(A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1338,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1324])).

tff(c_1344,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_1338])).

tff(c_1345,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_1344])).

tff(c_589,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k1_tops_1(A_86,B_87),B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_597,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_589])).

tff(c_602,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_597])).

tff(c_559,plain,(
    ! [A_82,B_83,C_84] :
      ( k7_subset_1(A_82,B_83,C_84) = k4_xboole_0(B_83,C_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_569,plain,(
    ! [C_85] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_85) = k4_xboole_0('#skF_2',C_85) ),
    inference(resolution,[status(thm)],[c_42,c_559])).

tff(c_575,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_133])).

tff(c_372,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k3_subset_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_383,plain,(
    ! [B_25,A_24] :
      ( k4_xboole_0(B_25,A_24) = k3_subset_1(B_25,A_24)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_372])).

tff(c_605,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_602,c_383])).

tff(c_607,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_605])).

tff(c_360,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k3_subset_1(A_70,B_71),k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_364,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k3_subset_1(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(resolution,[status(thm)],[c_360,c_24])).

tff(c_611,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_364])).

tff(c_968,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_611])).

tff(c_971,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_968])).

tff(c_975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_971])).

tff(c_976,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_977,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_1169,plain,(
    ! [A_119,B_120,C_121] :
      ( k4_subset_1(A_119,B_120,C_121) = k2_xboole_0(B_120,C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(A_119))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1254,plain,(
    ! [B_124,B_125,A_126] :
      ( k4_subset_1(B_124,B_125,A_126) = k2_xboole_0(B_125,A_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(B_124))
      | ~ r1_tarski(A_126,B_124) ) ),
    inference(resolution,[status(thm)],[c_26,c_1169])).

tff(c_1346,plain,(
    ! [A_134] :
      ( k4_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2'),A_134) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),A_134)
      | ~ r1_tarski(A_134,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_977,c_1254])).

tff(c_10,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k4_subset_1(A_20,B_21,k3_subset_1(A_20,B_21)) = k2_subset_1(A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_755,plain,(
    ! [A_93,B_94] :
      ( k4_subset_1(A_93,B_94,k3_subset_1(A_93,B_94)) = A_93
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_765,plain,(
    ! [B_95,A_96] :
      ( k4_subset_1(B_95,A_96,k3_subset_1(B_95,A_96)) = B_95
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(resolution,[status(thm)],[c_26,c_755])).

tff(c_774,plain,
    ( k4_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_765])).

tff(c_778,plain,(
    k4_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_774])).

tff(c_1356,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1346,c_778])).

tff(c_1379,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_1356])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_139,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(B_55,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_98])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_tarski(k2_tarski(A_7,B_8)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_145,plain,(
    ! [B_55,A_54] : k2_xboole_0(B_55,A_54) = k2_xboole_0(A_54,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_8])).

tff(c_269,plain,(
    ! [A_64,B_65] : k2_xboole_0(A_64,k2_xboole_0(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_284,plain,(
    ! [A_54,B_55] : k2_xboole_0(A_54,k2_xboole_0(B_55,A_54)) = k2_xboole_0(A_54,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_269])).

tff(c_1416,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1379,c_284])).

tff(c_1430,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_1416])).

tff(c_319,plain,(
    ! [A_68,B_69] : k2_xboole_0(A_68,k2_xboole_0(B_69,A_68)) = k2_xboole_0(A_68,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_269])).

tff(c_322,plain,(
    ! [B_69,A_68] : k2_xboole_0(k2_xboole_0(B_69,A_68),k2_xboole_0(A_68,B_69)) = k2_xboole_0(k2_xboole_0(B_69,A_68),A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_284])).

tff(c_399,plain,(
    ! [B_78,A_79] : k2_xboole_0(k2_xboole_0(B_78,A_79),k2_xboole_0(A_79,B_78)) = k2_xboole_0(A_79,B_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_145,c_322])).

tff(c_447,plain,(
    ! [B_55,A_54] : k2_xboole_0(k2_xboole_0(B_55,A_54),k2_xboole_0(B_55,A_54)) = k2_xboole_0(A_54,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_399])).

tff(c_1915,plain,(
    k2_xboole_0(k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')),k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1430,c_447])).

tff(c_1957,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_4,c_145,c_1379,c_145,c_1915])).

tff(c_1513,plain,(
    ! [A_136,B_137] :
      ( k4_subset_1(u1_struct_0(A_136),B_137,k2_tops_1(A_136,B_137)) = k2_pre_topc(A_136,B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1523,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1513])).

tff(c_1529,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1523])).

tff(c_813,plain,(
    ! [A_98,B_99] :
      ( m1_subset_1(k2_tops_1(A_98,B_99),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_830,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k2_tops_1(A_98,B_99),u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_813,c_24])).

tff(c_1273,plain,(
    ! [A_127] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_127) = k2_xboole_0('#skF_2',A_127)
      | ~ r1_tarski(A_127,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1254])).

tff(c_1277,plain,(
    ! [B_99] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_99)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_99))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_830,c_1273])).

tff(c_2296,plain,(
    ! [B_159] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_159)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_159))
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1277])).

tff(c_2311,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_2296])).

tff(c_2318,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1957,c_1529,c_2311])).

tff(c_2320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1345,c_2318])).

tff(c_2321,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_2321])).

tff(c_2456,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2520,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_48])).

tff(c_2804,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2803,c_2520])).

tff(c_3091,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3090,c_2804])).

tff(c_3286,plain,(
    ! [A_226,B_227] :
      ( k2_pre_topc(A_226,B_227) = B_227
      | ~ v4_pre_topc(B_227,A_226)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3300,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_3286])).

tff(c_3306,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2456,c_3300])).

tff(c_3811,plain,(
    ! [A_269,B_270] :
      ( k7_subset_1(u1_struct_0(A_269),k2_pre_topc(A_269,B_270),k1_tops_1(A_269,B_270)) = k2_tops_1(A_269,B_270)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3820,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3306,c_3811])).

tff(c_3824,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3090,c_2803,c_3820])).

tff(c_3826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3091,c_3824])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.00/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.94  
% 5.00/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.94  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 5.00/1.94  
% 5.00/1.94  %Foreground sorts:
% 5.00/1.94  
% 5.00/1.94  
% 5.00/1.94  %Background operators:
% 5.00/1.94  
% 5.00/1.94  
% 5.00/1.94  %Foreground operators:
% 5.00/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.00/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.00/1.94  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.00/1.94  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.00/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.00/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.00/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.00/1.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.00/1.94  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.00/1.94  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.00/1.94  tff('#skF_2', type, '#skF_2': $i).
% 5.00/1.94  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.00/1.94  tff('#skF_1', type, '#skF_1': $i).
% 5.00/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.00/1.94  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.00/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.00/1.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.00/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.00/1.94  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.00/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.00/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.00/1.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.00/1.94  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.00/1.94  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.00/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.00/1.94  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.00/1.94  
% 5.00/1.96  tff(f_125, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.00/1.96  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 5.00/1.96  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.00/1.96  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.00/1.96  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.00/1.96  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.00/1.96  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.00/1.96  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.00/1.96  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.00/1.96  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 5.00/1.96  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 5.00/1.96  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.00/1.96  tff(f_33, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.00/1.96  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.00/1.96  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.00/1.96  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.00/1.96  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.00/1.96  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.00/1.96  tff(c_3070, plain, (![A_217, B_218]: (r1_tarski(k1_tops_1(A_217, B_218), B_218) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.00/1.96  tff(c_3078, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_3070])).
% 5.00/1.96  tff(c_3083, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3078])).
% 5.00/1.96  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.00/1.96  tff(c_2687, plain, (![A_192, B_193]: (k4_xboole_0(A_192, B_193)=k3_subset_1(A_192, B_193) | ~m1_subset_1(B_193, k1_zfmisc_1(A_192)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.00/1.96  tff(c_2694, plain, (![B_25, A_24]: (k4_xboole_0(B_25, A_24)=k3_subset_1(B_25, A_24) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_2687])).
% 5.00/1.96  tff(c_3090, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3083, c_2694])).
% 5.00/1.96  tff(c_2794, plain, (![A_202, B_203, C_204]: (k7_subset_1(A_202, B_203, C_204)=k4_xboole_0(B_203, C_204) | ~m1_subset_1(B_203, k1_zfmisc_1(A_202)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.00/1.96  tff(c_2803, plain, (![C_204]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_204)=k4_xboole_0('#skF_2', C_204))), inference(resolution, [status(thm)], [c_42, c_2794])).
% 5.00/1.96  tff(c_54, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.00/1.96  tff(c_133, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 5.00/1.96  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.00/1.96  tff(c_267, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 5.00/1.96  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.00/1.96  tff(c_1324, plain, (![B_132, A_133]: (v4_pre_topc(B_132, A_133) | k2_pre_topc(A_133, B_132)!=B_132 | ~v2_pre_topc(A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.00/1.96  tff(c_1338, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1324])).
% 5.00/1.96  tff(c_1344, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_1338])).
% 5.00/1.96  tff(c_1345, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_267, c_1344])).
% 5.00/1.96  tff(c_589, plain, (![A_86, B_87]: (r1_tarski(k1_tops_1(A_86, B_87), B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.00/1.96  tff(c_597, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_589])).
% 5.00/1.96  tff(c_602, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_597])).
% 5.00/1.96  tff(c_559, plain, (![A_82, B_83, C_84]: (k7_subset_1(A_82, B_83, C_84)=k4_xboole_0(B_83, C_84) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.00/1.96  tff(c_569, plain, (![C_85]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_85)=k4_xboole_0('#skF_2', C_85))), inference(resolution, [status(thm)], [c_42, c_559])).
% 5.00/1.96  tff(c_575, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_569, c_133])).
% 5.00/1.96  tff(c_372, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k3_subset_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.00/1.96  tff(c_383, plain, (![B_25, A_24]: (k4_xboole_0(B_25, A_24)=k3_subset_1(B_25, A_24) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_372])).
% 5.00/1.96  tff(c_605, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_602, c_383])).
% 5.00/1.96  tff(c_607, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_575, c_605])).
% 5.00/1.96  tff(c_360, plain, (![A_70, B_71]: (m1_subset_1(k3_subset_1(A_70, B_71), k1_zfmisc_1(A_70)) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.00/1.96  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.00/1.96  tff(c_364, plain, (![A_70, B_71]: (r1_tarski(k3_subset_1(A_70, B_71), A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(resolution, [status(thm)], [c_360, c_24])).
% 5.00/1.96  tff(c_611, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_364])).
% 5.00/1.96  tff(c_968, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_611])).
% 5.00/1.96  tff(c_971, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_26, c_968])).
% 5.00/1.96  tff(c_975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_602, c_971])).
% 5.00/1.96  tff(c_976, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_611])).
% 5.00/1.96  tff(c_977, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_611])).
% 5.00/1.96  tff(c_1169, plain, (![A_119, B_120, C_121]: (k4_subset_1(A_119, B_120, C_121)=k2_xboole_0(B_120, C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(A_119)) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.00/1.96  tff(c_1254, plain, (![B_124, B_125, A_126]: (k4_subset_1(B_124, B_125, A_126)=k2_xboole_0(B_125, A_126) | ~m1_subset_1(B_125, k1_zfmisc_1(B_124)) | ~r1_tarski(A_126, B_124))), inference(resolution, [status(thm)], [c_26, c_1169])).
% 5.00/1.96  tff(c_1346, plain, (![A_134]: (k4_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'), A_134)=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), A_134) | ~r1_tarski(A_134, '#skF_2'))), inference(resolution, [status(thm)], [c_977, c_1254])).
% 5.00/1.96  tff(c_10, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.00/1.96  tff(c_20, plain, (![A_20, B_21]: (k4_subset_1(A_20, B_21, k3_subset_1(A_20, B_21))=k2_subset_1(A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.00/1.96  tff(c_755, plain, (![A_93, B_94]: (k4_subset_1(A_93, B_94, k3_subset_1(A_93, B_94))=A_93 | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 5.00/1.96  tff(c_765, plain, (![B_95, A_96]: (k4_subset_1(B_95, A_96, k3_subset_1(B_95, A_96))=B_95 | ~r1_tarski(A_96, B_95))), inference(resolution, [status(thm)], [c_26, c_755])).
% 5.00/1.96  tff(c_774, plain, (k4_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_607, c_765])).
% 5.00/1.96  tff(c_778, plain, (k4_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_602, c_774])).
% 5.00/1.96  tff(c_1356, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1346, c_778])).
% 5.00/1.96  tff(c_1379, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_976, c_1356])).
% 5.00/1.96  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.00/1.96  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.00/1.96  tff(c_98, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.00/1.96  tff(c_139, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(B_55, A_54))), inference(superposition, [status(thm), theory('equality')], [c_6, c_98])).
% 5.00/1.96  tff(c_8, plain, (![A_7, B_8]: (k3_tarski(k2_tarski(A_7, B_8))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.00/1.96  tff(c_145, plain, (![B_55, A_54]: (k2_xboole_0(B_55, A_54)=k2_xboole_0(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_139, c_8])).
% 5.00/1.96  tff(c_269, plain, (![A_64, B_65]: (k2_xboole_0(A_64, k2_xboole_0(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.00/1.96  tff(c_284, plain, (![A_54, B_55]: (k2_xboole_0(A_54, k2_xboole_0(B_55, A_54))=k2_xboole_0(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_145, c_269])).
% 5.00/1.96  tff(c_1416, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1379, c_284])).
% 5.00/1.96  tff(c_1430, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_1416])).
% 5.00/1.96  tff(c_319, plain, (![A_68, B_69]: (k2_xboole_0(A_68, k2_xboole_0(B_69, A_68))=k2_xboole_0(A_68, B_69))), inference(superposition, [status(thm), theory('equality')], [c_145, c_269])).
% 5.00/1.96  tff(c_322, plain, (![B_69, A_68]: (k2_xboole_0(k2_xboole_0(B_69, A_68), k2_xboole_0(A_68, B_69))=k2_xboole_0(k2_xboole_0(B_69, A_68), A_68))), inference(superposition, [status(thm), theory('equality')], [c_319, c_284])).
% 5.00/1.96  tff(c_399, plain, (![B_78, A_79]: (k2_xboole_0(k2_xboole_0(B_78, A_79), k2_xboole_0(A_79, B_78))=k2_xboole_0(A_79, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_145, c_322])).
% 5.00/1.96  tff(c_447, plain, (![B_55, A_54]: (k2_xboole_0(k2_xboole_0(B_55, A_54), k2_xboole_0(B_55, A_54))=k2_xboole_0(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_145, c_399])).
% 5.00/1.96  tff(c_1915, plain, (k2_xboole_0(k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')), k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2')))=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1430, c_447])).
% 5.00/1.96  tff(c_1957, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1379, c_4, c_145, c_1379, c_145, c_1915])).
% 5.00/1.96  tff(c_1513, plain, (![A_136, B_137]: (k4_subset_1(u1_struct_0(A_136), B_137, k2_tops_1(A_136, B_137))=k2_pre_topc(A_136, B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.00/1.96  tff(c_1523, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1513])).
% 5.00/1.96  tff(c_1529, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1523])).
% 5.00/1.96  tff(c_813, plain, (![A_98, B_99]: (m1_subset_1(k2_tops_1(A_98, B_99), k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.00/1.96  tff(c_830, plain, (![A_98, B_99]: (r1_tarski(k2_tops_1(A_98, B_99), u1_struct_0(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_813, c_24])).
% 5.00/1.96  tff(c_1273, plain, (![A_127]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_127)=k2_xboole_0('#skF_2', A_127) | ~r1_tarski(A_127, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_1254])).
% 5.00/1.96  tff(c_1277, plain, (![B_99]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_99))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_99)) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_830, c_1273])).
% 5.00/1.96  tff(c_2296, plain, (![B_159]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_159))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_159)) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1277])).
% 5.00/1.96  tff(c_2311, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_2296])).
% 5.00/1.96  tff(c_2318, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1957, c_1529, c_2311])).
% 5.00/1.96  tff(c_2320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1345, c_2318])).
% 5.00/1.96  tff(c_2321, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 5.00/1.96  tff(c_2455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_2321])).
% 5.00/1.96  tff(c_2456, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 5.00/1.96  tff(c_2520, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_48])).
% 5.00/1.96  tff(c_2804, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2803, c_2520])).
% 5.00/1.96  tff(c_3091, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3090, c_2804])).
% 5.00/1.96  tff(c_3286, plain, (![A_226, B_227]: (k2_pre_topc(A_226, B_227)=B_227 | ~v4_pre_topc(B_227, A_226) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.00/1.96  tff(c_3300, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_3286])).
% 5.00/1.96  tff(c_3306, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2456, c_3300])).
% 5.00/1.96  tff(c_3811, plain, (![A_269, B_270]: (k7_subset_1(u1_struct_0(A_269), k2_pre_topc(A_269, B_270), k1_tops_1(A_269, B_270))=k2_tops_1(A_269, B_270) | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0(A_269))) | ~l1_pre_topc(A_269))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.00/1.96  tff(c_3820, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3306, c_3811])).
% 5.00/1.96  tff(c_3824, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3090, c_2803, c_3820])).
% 5.00/1.96  tff(c_3826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3091, c_3824])).
% 5.00/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.96  
% 5.00/1.96  Inference rules
% 5.00/1.96  ----------------------
% 5.00/1.96  #Ref     : 0
% 5.00/1.96  #Sup     : 911
% 5.00/1.96  #Fact    : 0
% 5.00/1.96  #Define  : 0
% 5.00/1.96  #Split   : 3
% 5.00/1.96  #Chain   : 0
% 5.00/1.96  #Close   : 0
% 5.00/1.96  
% 5.00/1.96  Ordering : KBO
% 5.00/1.96  
% 5.00/1.96  Simplification rules
% 5.00/1.96  ----------------------
% 5.00/1.96  #Subsume      : 80
% 5.00/1.96  #Demod        : 1027
% 5.00/1.96  #Tautology    : 601
% 5.00/1.96  #SimpNegUnit  : 4
% 5.00/1.96  #BackRed      : 5
% 5.00/1.96  
% 5.00/1.96  #Partial instantiations: 0
% 5.00/1.96  #Strategies tried      : 1
% 5.00/1.96  
% 5.00/1.96  Timing (in seconds)
% 5.00/1.96  ----------------------
% 5.00/1.96  Preprocessing        : 0.33
% 5.00/1.96  Parsing              : 0.17
% 5.00/1.96  CNF conversion       : 0.02
% 5.00/1.96  Main loop            : 0.85
% 5.00/1.96  Inferencing          : 0.26
% 5.00/1.96  Reduction            : 0.39
% 5.00/1.96  Demodulation         : 0.32
% 5.00/1.96  BG Simplification    : 0.03
% 5.00/1.96  Subsumption          : 0.12
% 5.00/1.96  Abstraction          : 0.05
% 5.00/1.96  MUC search           : 0.00
% 5.00/1.96  Cooper               : 0.00
% 5.00/1.96  Total                : 1.23
% 5.00/1.96  Index Insertion      : 0.00
% 5.00/1.96  Index Deletion       : 0.00
% 5.00/1.97  Index Matching       : 0.00
% 5.00/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
