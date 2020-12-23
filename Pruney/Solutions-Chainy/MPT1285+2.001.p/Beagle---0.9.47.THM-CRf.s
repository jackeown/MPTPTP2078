%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:23 EST 2020

% Result     : Theorem 56.29s
% Output     : CNFRefutation 56.42s
% Verified   : 
% Statistics : Number of formulae       :  305 (1285 expanded)
%              Number of leaves         :   42 ( 459 expanded)
%              Depth                    :   14
%              Number of atoms          :  597 (3771 expanded)
%              Number of equality atoms :  139 ( 623 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v4_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v3_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v6_tops_1(D,B) )
                      & ( v6_tops_1(C,A)
                       => ( v3_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_79,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_150538,plain,(
    ! [B_1440,A_1441] :
      ( r1_tarski(B_1440,k2_pre_topc(A_1441,B_1440))
      | ~ m1_subset_1(B_1440,k1_zfmisc_1(u1_struct_0(A_1441)))
      | ~ l1_pre_topc(A_1441) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_150545,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_150538])).

tff(c_150552,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_150545])).

tff(c_144863,plain,(
    ! [A_1296,B_1297] :
      ( r1_tarski(A_1296,B_1297)
      | ~ m1_subset_1(A_1296,k1_zfmisc_1(B_1297)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_144871,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_144863])).

tff(c_150065,plain,(
    ! [A_1415,B_1416] :
      ( k3_xboole_0(A_1415,B_1416) = A_1415
      | ~ r1_tarski(A_1415,B_1416) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150078,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_144871,c_150065])).

tff(c_14,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_144848,plain,(
    ! [A_1294,B_1295] : k1_setfam_1(k2_tarski(A_1294,B_1295)) = k3_xboole_0(A_1294,B_1295) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_150134,plain,(
    ! [B_1422,A_1423] : k1_setfam_1(k2_tarski(B_1422,A_1423)) = k3_xboole_0(A_1423,B_1422) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_144848])).

tff(c_18,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_150140,plain,(
    ! [B_1422,A_1423] : k3_xboole_0(B_1422,A_1423) = k3_xboole_0(A_1423,B_1422) ),
    inference(superposition,[status(thm),theory(equality)],[c_150134,c_18])).

tff(c_150430,plain,(
    ! [A_1438,B_1439] :
      ( k4_xboole_0(A_1438,B_1439) = k3_subset_1(A_1438,B_1439)
      | ~ m1_subset_1(B_1439,k1_zfmisc_1(A_1438)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_150442,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_150430])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_150478,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_xboole_0(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_150442,c_12])).

tff(c_150486,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150078,c_150140,c_150478])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_150481,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_150442,c_10])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_151915,plain,(
    ! [B_1466,A_1467] :
      ( k4_xboole_0(B_1466,A_1467) = k3_subset_1(B_1466,A_1467)
      | ~ r1_tarski(A_1467,B_1466) ) ),
    inference(resolution,[status(thm)],[c_22,c_150430])).

tff(c_151927,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_150481,c_151915])).

tff(c_151953,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150486,c_151927])).

tff(c_151044,plain,(
    ! [A_1450,B_1451] :
      ( k2_pre_topc(A_1450,B_1451) = B_1451
      | ~ v4_pre_topc(B_1451,A_1450)
      | ~ m1_subset_1(B_1451,k1_zfmisc_1(u1_struct_0(A_1450)))
      | ~ l1_pre_topc(A_1450) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_155064,plain,(
    ! [A_1524,A_1525] :
      ( k2_pre_topc(A_1524,A_1525) = A_1525
      | ~ v4_pre_topc(A_1525,A_1524)
      | ~ l1_pre_topc(A_1524)
      | ~ r1_tarski(A_1525,u1_struct_0(A_1524)) ) ),
    inference(resolution,[status(thm)],[c_22,c_151044])).

tff(c_172965,plain,(
    ! [A_1666,B_1667] :
      ( k2_pre_topc(A_1666,k4_xboole_0(u1_struct_0(A_1666),B_1667)) = k4_xboole_0(u1_struct_0(A_1666),B_1667)
      | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(A_1666),B_1667),A_1666)
      | ~ l1_pre_topc(A_1666) ) ),
    inference(resolution,[status(thm)],[c_10,c_155064])).

tff(c_173005,plain,
    ( k2_pre_topc('#skF_1',k4_xboole_0(u1_struct_0('#skF_1'),'#skF_3')) = k4_xboole_0(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_150442,c_172965])).

tff(c_173032,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_150442,c_150442,c_173005])).

tff(c_173442,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_173032])).

tff(c_145880,plain,(
    ! [A_1337,B_1338] :
      ( m1_subset_1(k2_pre_topc(A_1337,B_1338),k1_zfmisc_1(u1_struct_0(A_1337)))
      | ~ m1_subset_1(B_1338,k1_zfmisc_1(u1_struct_0(A_1337)))
      | ~ l1_pre_topc(A_1337) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_150039,plain,(
    ! [A_1411,B_1412] :
      ( r1_tarski(k2_pre_topc(A_1411,B_1412),u1_struct_0(A_1411))
      | ~ m1_subset_1(B_1412,k1_zfmisc_1(u1_struct_0(A_1411)))
      | ~ l1_pre_topc(A_1411) ) ),
    inference(resolution,[status(thm)],[c_145880,c_20])).

tff(c_64,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_144872,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_72,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_109,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_147183,plain,(
    ! [A_1364,B_1365] :
      ( k1_tops_1(A_1364,k2_pre_topc(A_1364,B_1365)) = B_1365
      | ~ v6_tops_1(B_1365,A_1364)
      | ~ m1_subset_1(B_1365,k1_zfmisc_1(u1_struct_0(A_1364)))
      | ~ l1_pre_topc(A_1364) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_147192,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_147183])).

tff(c_147200,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_109,c_147192])).

tff(c_145612,plain,(
    ! [A_1331,B_1332] :
      ( v3_pre_topc(k1_tops_1(A_1331,B_1332),A_1331)
      | ~ m1_subset_1(B_1332,k1_zfmisc_1(u1_struct_0(A_1331)))
      | ~ l1_pre_topc(A_1331)
      | ~ v2_pre_topc(A_1331) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_150020,plain,(
    ! [A_1409,A_1410] :
      ( v3_pre_topc(k1_tops_1(A_1409,A_1410),A_1409)
      | ~ l1_pre_topc(A_1409)
      | ~ v2_pre_topc(A_1409)
      | ~ r1_tarski(A_1410,u1_struct_0(A_1409)) ) ),
    inference(resolution,[status(thm)],[c_22,c_145612])).

tff(c_150023,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_147200,c_150020])).

tff(c_150028,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_150023])).

tff(c_150029,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_144872,c_150028])).

tff(c_150042,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_150039,c_150029])).

tff(c_150054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_150042])).

tff(c_150056,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_46,plain,(
    ! [B_38,A_36] :
      ( v4_pre_topc(B_38,A_36)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_36),B_38),A_36)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_152113,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_151953,c_46])).

tff(c_152117,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_150056,c_152113])).

tff(c_208953,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_173442,c_152117])).

tff(c_208956,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_208953])).

tff(c_208960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150481,c_208956])).

tff(c_208961,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_173032])).

tff(c_32,plain,(
    ! [A_25,B_27] :
      ( k3_subset_1(u1_struct_0(A_25),k2_pre_topc(A_25,k3_subset_1(u1_struct_0(A_25),B_27))) = k1_tops_1(A_25,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_209012,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_208961,c_32])).

tff(c_209052,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_151953,c_209012])).

tff(c_68,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_110,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49070,plain,(
    ! [B_581,A_582] :
      ( r1_tarski(B_581,k2_pre_topc(A_582,B_581))
      | ~ m1_subset_1(B_581,k1_zfmisc_1(u1_struct_0(A_582)))
      | ~ l1_pre_topc(A_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_49075,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_49070])).

tff(c_49081,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_49075])).

tff(c_5729,plain,(
    ! [B_202,A_203] :
      ( r1_tarski(B_202,k2_pre_topc(A_203,B_202))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5736,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_5729])).

tff(c_5743,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5736])).

tff(c_146,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_158,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_146])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5414,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_158,c_8])).

tff(c_131,plain,(
    ! [A_67,B_68] : k1_setfam_1(k2_tarski(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5426,plain,(
    ! [B_184,A_185] : k1_setfam_1(k2_tarski(B_184,A_185)) = k3_xboole_0(A_185,B_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_131])).

tff(c_5432,plain,(
    ! [B_184,A_185] : k3_xboole_0(B_184,A_185) = k3_xboole_0(A_185,B_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_5426,c_18])).

tff(c_5575,plain,(
    ! [A_196,B_197] :
      ( k4_xboole_0(A_196,B_197) = k3_subset_1(A_196,B_197)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(A_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5587,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_5575])).

tff(c_5610,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_xboole_0(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5587,c_12])).

tff(c_5616,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5414,c_5432,c_5610])).

tff(c_5613,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5587,c_10])).

tff(c_7308,plain,(
    ! [B_236,A_237] :
      ( k4_xboole_0(B_236,A_237) = k3_subset_1(B_236,A_237)
      | ~ r1_tarski(A_237,B_236) ) ),
    inference(resolution,[status(thm)],[c_22,c_5575])).

tff(c_7320,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_5613,c_7308])).

tff(c_7346,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5616,c_7320])).

tff(c_6261,plain,(
    ! [A_216,B_217] :
      ( k2_pre_topc(A_216,B_217) = B_217
      | ~ v4_pre_topc(B_217,A_216)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_9929,plain,(
    ! [A_284,A_285] :
      ( k2_pre_topc(A_284,A_285) = A_285
      | ~ v4_pre_topc(A_285,A_284)
      | ~ l1_pre_topc(A_284)
      | ~ r1_tarski(A_285,u1_struct_0(A_284)) ) ),
    inference(resolution,[status(thm)],[c_22,c_6261])).

tff(c_29418,plain,(
    ! [A_438,B_439] :
      ( k2_pre_topc(A_438,k4_xboole_0(u1_struct_0(A_438),B_439)) = k4_xboole_0(u1_struct_0(A_438),B_439)
      | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(A_438),B_439),A_438)
      | ~ l1_pre_topc(A_438) ) ),
    inference(resolution,[status(thm)],[c_10,c_9929])).

tff(c_29458,plain,
    ( k2_pre_topc('#skF_1',k4_xboole_0(u1_struct_0('#skF_1'),'#skF_3')) = k4_xboole_0(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5587,c_29418])).

tff(c_29485,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5587,c_5587,c_29458])).

tff(c_29492,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_29485])).

tff(c_1016,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1(k2_pre_topc(A_103,B_104),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1031,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(k2_pre_topc(A_103,B_104),u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_1016,c_20])).

tff(c_163,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1596,plain,(
    ! [A_113,B_114] :
      ( k1_tops_1(A_113,k2_pre_topc(A_113,B_114)) = B_114
      | ~ v6_tops_1(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1605,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1596])).

tff(c_1613,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_109,c_1605])).

tff(c_1142,plain,(
    ! [A_105,B_106] :
      ( v3_pre_topc(k1_tops_1(A_105,B_106),A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5395,plain,(
    ! [A_182,A_183] :
      ( v3_pre_topc(k1_tops_1(A_182,A_183),A_182)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | ~ r1_tarski(A_183,u1_struct_0(A_182)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1142])).

tff(c_5398,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1613,c_5395])).

tff(c_5400,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5398])).

tff(c_5401,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_5400])).

tff(c_5404,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1031,c_5401])).

tff(c_5408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_5404])).

tff(c_5410,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_7520,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7346,c_46])).

tff(c_7526,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5410,c_7520])).

tff(c_48722,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_29492,c_7526])).

tff(c_48725,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_48722])).

tff(c_48729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5613,c_48725])).

tff(c_48730,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_29485])).

tff(c_48776,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_48730,c_32])).

tff(c_48816,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_7346,c_48776])).

tff(c_5409,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_5425,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5409])).

tff(c_7851,plain,(
    ! [A_250,B_251] :
      ( k1_tops_1(A_250,k2_pre_topc(A_250,B_251)) = B_251
      | ~ v6_tops_1(B_251,A_250)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ l1_pre_topc(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_7860,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_7851])).

tff(c_7868,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_109,c_7860])).

tff(c_8988,plain,(
    ! [B_274,A_275] :
      ( v4_tops_1(B_274,A_275)
      | ~ r1_tarski(B_274,k2_pre_topc(A_275,k1_tops_1(A_275,B_274)))
      | ~ r1_tarski(k1_tops_1(A_275,k2_pre_topc(A_275,B_274)),B_274)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ l1_pre_topc(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8998,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7868,c_8988])).

tff(c_9002,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_6,c_8998])).

tff(c_9003,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_5425,c_9002])).

tff(c_48826,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48816,c_9003])).

tff(c_48832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5743,c_48826])).

tff(c_48833,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_5409])).

tff(c_48835,plain,(
    ! [A_565,B_566] : k1_setfam_1(k2_tarski(A_565,B_566)) = k3_xboole_0(B_566,A_565) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_131])).

tff(c_48841,plain,(
    ! [B_566,A_565] : k3_xboole_0(B_566,A_565) = k3_xboole_0(A_565,B_566) ),
    inference(superposition,[status(thm),theory(equality)],[c_48835,c_18])).

tff(c_51441,plain,(
    ! [A_633,B_634] :
      ( r1_tarski(k1_tops_1(A_633,k2_pre_topc(A_633,B_634)),B_634)
      | ~ v4_tops_1(B_634,A_633)
      | ~ m1_subset_1(B_634,k1_zfmisc_1(u1_struct_0(A_633)))
      | ~ l1_pre_topc(A_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_51449,plain,(
    ! [A_633,B_634] :
      ( k3_xboole_0(k1_tops_1(A_633,k2_pre_topc(A_633,B_634)),B_634) = k1_tops_1(A_633,k2_pre_topc(A_633,B_634))
      | ~ v4_tops_1(B_634,A_633)
      | ~ m1_subset_1(B_634,k1_zfmisc_1(u1_struct_0(A_633)))
      | ~ l1_pre_topc(A_633) ) ),
    inference(resolution,[status(thm)],[c_51441,c_8])).

tff(c_141438,plain,(
    ! [B_1279,A_1280] :
      ( k3_xboole_0(B_1279,k1_tops_1(A_1280,k2_pre_topc(A_1280,B_1279))) = k1_tops_1(A_1280,k2_pre_topc(A_1280,B_1279))
      | ~ v4_tops_1(B_1279,A_1280)
      | ~ m1_subset_1(B_1279,k1_zfmisc_1(u1_struct_0(A_1280)))
      | ~ l1_pre_topc(A_1280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48841,c_51449])).

tff(c_141447,plain,
    ( k3_xboole_0('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_141438])).

tff(c_141457,plain,(
    k3_xboole_0('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48833,c_141447])).

tff(c_49553,plain,(
    ! [A_595,B_596] :
      ( m1_subset_1(k2_pre_topc(A_595,B_596),k1_zfmisc_1(u1_struct_0(A_595)))
      | ~ m1_subset_1(B_596,k1_zfmisc_1(u1_struct_0(A_595)))
      | ~ l1_pre_topc(A_595) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53724,plain,(
    ! [A_669,B_670] :
      ( r1_tarski(k2_pre_topc(A_669,B_670),u1_struct_0(A_669))
      | ~ m1_subset_1(B_670,k1_zfmisc_1(u1_struct_0(A_669)))
      | ~ l1_pre_topc(A_669) ) ),
    inference(resolution,[status(thm)],[c_49553,c_20])).

tff(c_53732,plain,(
    ! [A_669,B_670] :
      ( k3_xboole_0(k2_pre_topc(A_669,B_670),u1_struct_0(A_669)) = k2_pre_topc(A_669,B_670)
      | ~ m1_subset_1(B_670,k1_zfmisc_1(u1_struct_0(A_669)))
      | ~ l1_pre_topc(A_669) ) ),
    inference(resolution,[status(thm)],[c_53724,c_8])).

tff(c_119692,plain,(
    ! [A_1125,B_1126] :
      ( k3_xboole_0(u1_struct_0(A_1125),k2_pre_topc(A_1125,B_1126)) = k2_pre_topc(A_1125,B_1126)
      | ~ m1_subset_1(B_1126,k1_zfmisc_1(u1_struct_0(A_1125)))
      | ~ l1_pre_topc(A_1125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48841,c_53732])).

tff(c_119701,plain,
    ( k3_xboole_0(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k2_pre_topc('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_119692])).

tff(c_119711,plain,(
    k3_xboole_0(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_119701])).

tff(c_48912,plain,(
    ! [A_571,B_572] : k4_xboole_0(A_571,k4_xboole_0(A_571,B_572)) = k3_xboole_0(A_571,B_572) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48921,plain,(
    ! [A_571,B_572] : r1_tarski(k3_xboole_0(A_571,B_572),A_571) ),
    inference(superposition,[status(thm),theory(equality)],[c_48912,c_10])).

tff(c_119948,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_119711,c_48921])).

tff(c_157,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_146])).

tff(c_162,plain,(
    k3_xboole_0('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_157,c_8])).

tff(c_48984,plain,(
    ! [A_577,B_578] :
      ( k4_xboole_0(A_577,B_578) = k3_subset_1(A_577,B_578)
      | ~ m1_subset_1(B_578,k1_zfmisc_1(A_577)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48995,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_4') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_48984])).

tff(c_49039,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_xboole_0(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48995,c_12])).

tff(c_49046,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_48841,c_49039])).

tff(c_49042,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48995,c_10])).

tff(c_50712,plain,(
    ! [B_613,A_614] :
      ( k4_xboole_0(B_613,A_614) = k3_subset_1(B_613,A_614)
      | ~ r1_tarski(A_614,B_613) ) ),
    inference(resolution,[status(thm)],[c_22,c_48984])).

tff(c_50727,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_49042,c_50712])).

tff(c_50752,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49046,c_50727])).

tff(c_49798,plain,(
    ! [A_599,B_600] :
      ( k2_pre_topc(A_599,B_600) = B_600
      | ~ v4_pre_topc(B_600,A_599)
      | ~ m1_subset_1(B_600,k1_zfmisc_1(u1_struct_0(A_599)))
      | ~ l1_pre_topc(A_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_53746,plain,(
    ! [A_671,A_672] :
      ( k2_pre_topc(A_671,A_672) = A_672
      | ~ v4_pre_topc(A_672,A_671)
      | ~ l1_pre_topc(A_671)
      | ~ r1_tarski(A_672,u1_struct_0(A_671)) ) ),
    inference(resolution,[status(thm)],[c_22,c_49798])).

tff(c_123415,plain,(
    ! [A_1138,B_1139] :
      ( k2_pre_topc(A_1138,k4_xboole_0(u1_struct_0(A_1138),B_1139)) = k4_xboole_0(u1_struct_0(A_1138),B_1139)
      | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(A_1138),B_1139),A_1138)
      | ~ l1_pre_topc(A_1138) ) ),
    inference(resolution,[status(thm)],[c_10,c_53746])).

tff(c_123455,plain,
    ( k2_pre_topc('#skF_2',k4_xboole_0(u1_struct_0('#skF_2'),'#skF_4')) = k4_xboole_0(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_48995,c_123415])).

tff(c_123480,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48995,c_48995,c_123455])).

tff(c_124420,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_123480])).

tff(c_48834,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_5409])).

tff(c_66,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_48892,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5410,c_48834,c_66])).

tff(c_51242,plain,(
    ! [B_629,A_630] :
      ( v4_pre_topc(B_629,A_630)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_630),B_629),A_630)
      | ~ m1_subset_1(B_629,k1_zfmisc_1(u1_struct_0(A_630)))
      | ~ l1_pre_topc(A_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_51245,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_50752,c_51242])).

tff(c_51265,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48892,c_51245])).

tff(c_138304,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_124420,c_51265])).

tff(c_138307,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_138304])).

tff(c_138311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49042,c_138307])).

tff(c_138312,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_123480])).

tff(c_138442,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_138312,c_32])).

tff(c_138482,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50752,c_138442])).

tff(c_52051,plain,(
    ! [A_647,B_648,C_649] :
      ( r1_tarski(k1_tops_1(A_647,B_648),k1_tops_1(A_647,C_649))
      | ~ r1_tarski(B_648,C_649)
      | ~ m1_subset_1(C_649,k1_zfmisc_1(u1_struct_0(A_647)))
      | ~ m1_subset_1(B_648,k1_zfmisc_1(u1_struct_0(A_647)))
      | ~ l1_pre_topc(A_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_109045,plain,(
    ! [A_1048,B_1049,C_1050] :
      ( k3_xboole_0(k1_tops_1(A_1048,B_1049),k1_tops_1(A_1048,C_1050)) = k1_tops_1(A_1048,B_1049)
      | ~ r1_tarski(B_1049,C_1050)
      | ~ m1_subset_1(C_1050,k1_zfmisc_1(u1_struct_0(A_1048)))
      | ~ m1_subset_1(B_1049,k1_zfmisc_1(u1_struct_0(A_1048)))
      | ~ l1_pre_topc(A_1048) ) ),
    inference(resolution,[status(thm)],[c_52051,c_8])).

tff(c_144652,plain,(
    ! [A_1290,B_1291,A_1292] :
      ( k3_xboole_0(k1_tops_1(A_1290,B_1291),k1_tops_1(A_1290,A_1292)) = k1_tops_1(A_1290,B_1291)
      | ~ r1_tarski(B_1291,A_1292)
      | ~ m1_subset_1(B_1291,k1_zfmisc_1(u1_struct_0(A_1290)))
      | ~ l1_pre_topc(A_1290)
      | ~ r1_tarski(A_1292,u1_struct_0(A_1290)) ) ),
    inference(resolution,[status(thm)],[c_22,c_109045])).

tff(c_144661,plain,(
    ! [A_1292] :
      ( k3_xboole_0(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2',A_1292)) = k1_tops_1('#skF_2','#skF_4')
      | ~ r1_tarski('#skF_4',A_1292)
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_1292,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_52,c_144652])).

tff(c_144678,plain,(
    ! [A_1293] :
      ( k3_xboole_0('#skF_4',k1_tops_1('#skF_2',A_1293)) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_1293)
      | ~ r1_tarski(A_1293,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_138482,c_138482,c_144661])).

tff(c_144681,plain,
    ( k3_xboole_0('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_119948,c_144678])).

tff(c_144721,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49081,c_141457,c_144681])).

tff(c_48930,plain,(
    ! [A_573,B_574] : r1_tarski(k3_xboole_0(A_573,B_574),A_573) ),
    inference(superposition,[status(thm),theory(equality)],[c_48912,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48951,plain,(
    ! [A_573,B_574] :
      ( k3_xboole_0(A_573,B_574) = A_573
      | ~ r1_tarski(A_573,k3_xboole_0(A_573,B_574)) ) ),
    inference(resolution,[status(thm)],[c_48930,c_2])).

tff(c_141704,plain,
    ( k3_xboole_0('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_141457,c_48951])).

tff(c_141837,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141457,c_141704])).

tff(c_144647,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_141837])).

tff(c_144738,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144721,c_144647])).

tff(c_144748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_144738])).

tff(c_144749,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_141837])).

tff(c_40,plain,(
    ! [B_33,A_31] :
      ( v6_tops_1(B_33,A_31)
      | k1_tops_1(A_31,k2_pre_topc(A_31,B_33)) != B_33
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_144808,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_144749,c_40])).

tff(c_144841,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_144808])).

tff(c_144843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_144841])).

tff(c_144845,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_62,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_150059,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150056,c_144845,c_62])).

tff(c_152499,plain,(
    ! [A_1482,B_1483] :
      ( k1_tops_1(A_1482,k2_pre_topc(A_1482,B_1483)) = B_1483
      | ~ v6_tops_1(B_1483,A_1482)
      | ~ m1_subset_1(B_1483,k1_zfmisc_1(u1_struct_0(A_1482)))
      | ~ l1_pre_topc(A_1482) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_152508,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_152499])).

tff(c_152516,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_109,c_152508])).

tff(c_153811,plain,(
    ! [B_1510,A_1511] :
      ( v4_tops_1(B_1510,A_1511)
      | ~ r1_tarski(B_1510,k2_pre_topc(A_1511,k1_tops_1(A_1511,B_1510)))
      | ~ r1_tarski(k1_tops_1(A_1511,k2_pre_topc(A_1511,B_1510)),B_1510)
      | ~ m1_subset_1(B_1510,k1_zfmisc_1(u1_struct_0(A_1511)))
      | ~ l1_pre_topc(A_1511) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_153821,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_152516,c_153811])).

tff(c_153828,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_6,c_153821])).

tff(c_153829,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_150059,c_153828])).

tff(c_209061,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209052,c_153829])).

tff(c_209066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150552,c_209061])).

tff(c_209068,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_209070,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_209068,c_68])).

tff(c_209527,plain,(
    ! [B_1888,A_1889] :
      ( r1_tarski(B_1888,k2_pre_topc(A_1889,B_1888))
      | ~ m1_subset_1(B_1888,k1_zfmisc_1(u1_struct_0(A_1889)))
      | ~ l1_pre_topc(A_1889) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_209532,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_209527])).

tff(c_209538,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_209532])).

tff(c_70,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_209069,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_209068,c_70])).

tff(c_209071,plain,(
    ! [A_1859,B_1860] : k1_setfam_1(k2_tarski(A_1859,B_1860)) = k3_xboole_0(A_1859,B_1860) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_209171,plain,(
    ! [B_1872,A_1873] : k1_setfam_1(k2_tarski(B_1872,A_1873)) = k3_xboole_0(A_1873,B_1872) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_209071])).

tff(c_209177,plain,(
    ! [B_1872,A_1873] : k3_xboole_0(B_1872,A_1873) = k3_xboole_0(A_1873,B_1872) ),
    inference(superposition,[status(thm),theory(equality)],[c_209171,c_18])).

tff(c_211986,plain,(
    ! [A_1940,B_1941] :
      ( r1_tarski(k1_tops_1(A_1940,k2_pre_topc(A_1940,B_1941)),B_1941)
      | ~ v4_tops_1(B_1941,A_1940)
      | ~ m1_subset_1(B_1941,k1_zfmisc_1(u1_struct_0(A_1940)))
      | ~ l1_pre_topc(A_1940) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_211994,plain,(
    ! [A_1940,B_1941] :
      ( k3_xboole_0(k1_tops_1(A_1940,k2_pre_topc(A_1940,B_1941)),B_1941) = k1_tops_1(A_1940,k2_pre_topc(A_1940,B_1941))
      | ~ v4_tops_1(B_1941,A_1940)
      | ~ m1_subset_1(B_1941,k1_zfmisc_1(u1_struct_0(A_1940)))
      | ~ l1_pre_topc(A_1940) ) ),
    inference(resolution,[status(thm)],[c_211986,c_8])).

tff(c_248176,plain,(
    ! [B_2234,A_2235] :
      ( k3_xboole_0(B_2234,k1_tops_1(A_2235,k2_pre_topc(A_2235,B_2234))) = k1_tops_1(A_2235,k2_pre_topc(A_2235,B_2234))
      | ~ v4_tops_1(B_2234,A_2235)
      | ~ m1_subset_1(B_2234,k1_zfmisc_1(u1_struct_0(A_2235)))
      | ~ l1_pre_topc(A_2235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209177,c_211994])).

tff(c_248183,plain,
    ( k3_xboole_0('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_248176])).

tff(c_248190,plain,(
    k3_xboole_0('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_209069,c_248183])).

tff(c_210102,plain,(
    ! [A_1902,B_1903] :
      ( m1_subset_1(k2_pre_topc(A_1902,B_1903),k1_zfmisc_1(u1_struct_0(A_1902)))
      | ~ m1_subset_1(B_1903,k1_zfmisc_1(u1_struct_0(A_1902)))
      | ~ l1_pre_topc(A_1902) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_213590,plain,(
    ! [A_1968,B_1969] :
      ( r1_tarski(k2_pre_topc(A_1968,B_1969),u1_struct_0(A_1968))
      | ~ m1_subset_1(B_1969,k1_zfmisc_1(u1_struct_0(A_1968)))
      | ~ l1_pre_topc(A_1968) ) ),
    inference(resolution,[status(thm)],[c_210102,c_20])).

tff(c_213598,plain,(
    ! [A_1968,B_1969] :
      ( k3_xboole_0(k2_pre_topc(A_1968,B_1969),u1_struct_0(A_1968)) = k2_pre_topc(A_1968,B_1969)
      | ~ m1_subset_1(B_1969,k1_zfmisc_1(u1_struct_0(A_1968)))
      | ~ l1_pre_topc(A_1968) ) ),
    inference(resolution,[status(thm)],[c_213590,c_8])).

tff(c_227186,plain,(
    ! [A_2098,B_2099] :
      ( k3_xboole_0(u1_struct_0(A_2098),k2_pre_topc(A_2098,B_2099)) = k2_pre_topc(A_2098,B_2099)
      | ~ m1_subset_1(B_2099,k1_zfmisc_1(u1_struct_0(A_2098)))
      | ~ l1_pre_topc(A_2098) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209177,c_213598])).

tff(c_227193,plain,
    ( k3_xboole_0(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k2_pre_topc('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_227186])).

tff(c_227200,plain,(
    k3_xboole_0(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_227193])).

tff(c_209127,plain,(
    ! [A_1868,B_1869] : k4_xboole_0(A_1868,k4_xboole_0(A_1868,B_1869)) = k3_xboole_0(A_1868,B_1869) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_209136,plain,(
    ! [A_1868,B_1869] : r1_tarski(k3_xboole_0(A_1868,B_1869),A_1868) ),
    inference(superposition,[status(thm),theory(equality)],[c_209127,c_10])).

tff(c_227443,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_227200,c_209136])).

tff(c_209106,plain,(
    ! [A_1866,B_1867] :
      ( r1_tarski(A_1866,B_1867)
      | ~ m1_subset_1(A_1866,k1_zfmisc_1(B_1867)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_209117,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_209106])).

tff(c_209122,plain,(
    k3_xboole_0('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_209117,c_8])).

tff(c_209435,plain,(
    ! [A_1886,B_1887] :
      ( k4_xboole_0(A_1886,B_1887) = k3_subset_1(A_1886,B_1887)
      | ~ m1_subset_1(B_1887,k1_zfmisc_1(A_1886)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_209446,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_4') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_209435])).

tff(c_211029,plain,(
    ! [B_1916,A_1917] :
      ( k4_xboole_0(B_1916,A_1917) = k3_subset_1(B_1916,A_1917)
      | ~ r1_tarski(A_1917,B_1916) ) ),
    inference(resolution,[status(thm)],[c_22,c_209435])).

tff(c_211059,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_10,c_211029])).

tff(c_211140,plain,(
    ! [A_1921,B_1922] : k3_subset_1(A_1921,k4_xboole_0(A_1921,B_1922)) = k3_xboole_0(A_1921,B_1922) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_211059])).

tff(c_211164,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_xboole_0(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_209446,c_211140])).

tff(c_211172,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209122,c_209177,c_211164])).

tff(c_209457,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_209446,c_10])).

tff(c_209975,plain,(
    ! [A_1900,B_1901] :
      ( k2_pre_topc(A_1900,B_1901) = B_1901
      | ~ v4_pre_topc(B_1901,A_1900)
      | ~ m1_subset_1(B_1901,k1_zfmisc_1(u1_struct_0(A_1900)))
      | ~ l1_pre_topc(A_1900) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_214000,plain,(
    ! [A_1974,A_1975] :
      ( k2_pre_topc(A_1974,A_1975) = A_1975
      | ~ v4_pre_topc(A_1975,A_1974)
      | ~ l1_pre_topc(A_1974)
      | ~ r1_tarski(A_1975,u1_struct_0(A_1974)) ) ),
    inference(resolution,[status(thm)],[c_22,c_209975])).

tff(c_230859,plain,(
    ! [A_2108,B_2109] :
      ( k2_pre_topc(A_2108,k4_xboole_0(u1_struct_0(A_2108),B_2109)) = k4_xboole_0(u1_struct_0(A_2108),B_2109)
      | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(A_2108),B_2109),A_2108)
      | ~ l1_pre_topc(A_2108) ) ),
    inference(resolution,[status(thm)],[c_10,c_214000])).

tff(c_230899,plain,
    ( k2_pre_topc('#skF_2',k4_xboole_0(u1_struct_0('#skF_2'),'#skF_4')) = k4_xboole_0(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_209446,c_230859])).

tff(c_230925,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_209446,c_209446,c_230899])).

tff(c_231382,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_230925])).

tff(c_209067,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_211794,plain,(
    ! [B_1936,A_1937] :
      ( v4_pre_topc(B_1936,A_1937)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_1937),B_1936),A_1937)
      | ~ m1_subset_1(B_1936,k1_zfmisc_1(u1_struct_0(A_1937)))
      | ~ l1_pre_topc(A_1937) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_211807,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_211172,c_211794])).

tff(c_211824,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_209067,c_211807])).

tff(c_243282,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_231382,c_211824])).

tff(c_243285,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_243282])).

tff(c_243289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209457,c_243285])).

tff(c_243290,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_230925])).

tff(c_243333,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_243290,c_32])).

tff(c_243371,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_211172,c_243333])).

tff(c_212572,plain,(
    ! [A_1955,B_1956,C_1957] :
      ( r1_tarski(k1_tops_1(A_1955,B_1956),k1_tops_1(A_1955,C_1957))
      | ~ r1_tarski(B_1956,C_1957)
      | ~ m1_subset_1(C_1957,k1_zfmisc_1(u1_struct_0(A_1955)))
      | ~ m1_subset_1(B_1956,k1_zfmisc_1(u1_struct_0(A_1955)))
      | ~ l1_pre_topc(A_1955) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_217736,plain,(
    ! [A_2024,B_2025,C_2026] :
      ( k3_xboole_0(k1_tops_1(A_2024,B_2025),k1_tops_1(A_2024,C_2026)) = k1_tops_1(A_2024,B_2025)
      | ~ r1_tarski(B_2025,C_2026)
      | ~ m1_subset_1(C_2026,k1_zfmisc_1(u1_struct_0(A_2024)))
      | ~ m1_subset_1(B_2025,k1_zfmisc_1(u1_struct_0(A_2024)))
      | ~ l1_pre_topc(A_2024) ) ),
    inference(resolution,[status(thm)],[c_212572,c_8])).

tff(c_249318,plain,(
    ! [A_2240,B_2241,A_2242] :
      ( k3_xboole_0(k1_tops_1(A_2240,B_2241),k1_tops_1(A_2240,A_2242)) = k1_tops_1(A_2240,B_2241)
      | ~ r1_tarski(B_2241,A_2242)
      | ~ m1_subset_1(B_2241,k1_zfmisc_1(u1_struct_0(A_2240)))
      | ~ l1_pre_topc(A_2240)
      | ~ r1_tarski(A_2242,u1_struct_0(A_2240)) ) ),
    inference(resolution,[status(thm)],[c_22,c_217736])).

tff(c_249325,plain,(
    ! [A_2242] :
      ( k3_xboole_0(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2',A_2242)) = k1_tops_1('#skF_2','#skF_4')
      | ~ r1_tarski('#skF_4',A_2242)
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_2242,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_52,c_249318])).

tff(c_249339,plain,(
    ! [A_2243] :
      ( k3_xboole_0('#skF_4',k1_tops_1('#skF_2',A_2243)) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_2243)
      | ~ r1_tarski(A_2243,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_243371,c_243371,c_249325])).

tff(c_249342,plain,
    ( k3_xboole_0('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_227443,c_249339])).

tff(c_249382,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209538,c_248190,c_249342])).

tff(c_249456,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_249382,c_40])).

tff(c_249489,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_249456])).

tff(c_249491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209070,c_249489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.32  % CPULimit   : 60
% 0.17/0.32  % DateTime   : Tue Dec  1 12:25:04 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 56.29/45.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.42/45.35  
% 56.42/45.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.42/45.35  %$ v6_tops_1 > v4_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 56.42/45.35  
% 56.42/45.35  %Foreground sorts:
% 56.42/45.35  
% 56.42/45.35  
% 56.42/45.35  %Background operators:
% 56.42/45.35  
% 56.42/45.35  
% 56.42/45.35  %Foreground operators:
% 56.42/45.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 56.42/45.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 56.42/45.35  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 56.42/45.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 56.42/45.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 56.42/45.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 56.42/45.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 56.42/45.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 56.42/45.35  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 56.42/45.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 56.42/45.35  tff('#skF_2', type, '#skF_2': $i).
% 56.42/45.35  tff('#skF_3', type, '#skF_3': $i).
% 56.42/45.35  tff('#skF_1', type, '#skF_1': $i).
% 56.42/45.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 56.42/45.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 56.42/45.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 56.42/45.35  tff('#skF_4', type, '#skF_4': $i).
% 56.42/45.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 56.42/45.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 56.42/45.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 56.42/45.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 56.42/45.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 56.42/45.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 56.42/45.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 56.42/45.35  
% 56.42/45.39  tff(f_161, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_tops_1)).
% 56.42/45.39  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 56.42/45.39  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 56.42/45.39  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 56.42/45.39  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 56.42/45.39  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 56.42/45.39  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 56.42/45.39  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 56.42/45.39  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 56.42/45.39  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 56.42/45.39  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 56.42/45.39  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tops_1)).
% 56.42/45.39  tff(f_114, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 56.42/45.39  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 56.42/45.39  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 56.42/45.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 56.42/45.39  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 56.42/45.39  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 56.42/45.39  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.42/45.39  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.42/45.39  tff(c_150538, plain, (![B_1440, A_1441]: (r1_tarski(B_1440, k2_pre_topc(A_1441, B_1440)) | ~m1_subset_1(B_1440, k1_zfmisc_1(u1_struct_0(A_1441))) | ~l1_pre_topc(A_1441))), inference(cnfTransformation, [status(thm)], [f_64])).
% 56.42/45.39  tff(c_150545, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_150538])).
% 56.42/45.39  tff(c_150552, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_150545])).
% 56.42/45.39  tff(c_144863, plain, (![A_1296, B_1297]: (r1_tarski(A_1296, B_1297) | ~m1_subset_1(A_1296, k1_zfmisc_1(B_1297)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 56.42/45.39  tff(c_144871, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_144863])).
% 56.42/45.39  tff(c_150065, plain, (![A_1415, B_1416]: (k3_xboole_0(A_1415, B_1416)=A_1415 | ~r1_tarski(A_1415, B_1416))), inference(cnfTransformation, [status(thm)], [f_35])).
% 56.42/45.39  tff(c_150078, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_144871, c_150065])).
% 56.42/45.39  tff(c_14, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 56.42/45.39  tff(c_144848, plain, (![A_1294, B_1295]: (k1_setfam_1(k2_tarski(A_1294, B_1295))=k3_xboole_0(A_1294, B_1295))), inference(cnfTransformation, [status(thm)], [f_47])).
% 56.42/45.39  tff(c_150134, plain, (![B_1422, A_1423]: (k1_setfam_1(k2_tarski(B_1422, A_1423))=k3_xboole_0(A_1423, B_1422))), inference(superposition, [status(thm), theory('equality')], [c_14, c_144848])).
% 56.42/45.39  tff(c_18, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 56.42/45.39  tff(c_150140, plain, (![B_1422, A_1423]: (k3_xboole_0(B_1422, A_1423)=k3_xboole_0(A_1423, B_1422))), inference(superposition, [status(thm), theory('equality')], [c_150134, c_18])).
% 56.42/45.39  tff(c_150430, plain, (![A_1438, B_1439]: (k4_xboole_0(A_1438, B_1439)=k3_subset_1(A_1438, B_1439) | ~m1_subset_1(B_1439, k1_zfmisc_1(A_1438)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 56.42/45.39  tff(c_150442, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_54, c_150430])).
% 56.42/45.39  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 56.42/45.39  tff(c_150478, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_xboole_0(u1_struct_0('#skF_1'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_150442, c_12])).
% 56.42/45.39  tff(c_150486, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_150078, c_150140, c_150478])).
% 56.42/45.39  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 56.42/45.39  tff(c_150481, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_150442, c_10])).
% 56.42/45.39  tff(c_22, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 56.42/45.39  tff(c_151915, plain, (![B_1466, A_1467]: (k4_xboole_0(B_1466, A_1467)=k3_subset_1(B_1466, A_1467) | ~r1_tarski(A_1467, B_1466))), inference(resolution, [status(thm)], [c_22, c_150430])).
% 56.42/45.39  tff(c_151927, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(resolution, [status(thm)], [c_150481, c_151915])).
% 56.42/45.39  tff(c_151953, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_150486, c_151927])).
% 56.42/45.39  tff(c_151044, plain, (![A_1450, B_1451]: (k2_pre_topc(A_1450, B_1451)=B_1451 | ~v4_pre_topc(B_1451, A_1450) | ~m1_subset_1(B_1451, k1_zfmisc_1(u1_struct_0(A_1450))) | ~l1_pre_topc(A_1450))), inference(cnfTransformation, [status(thm)], [f_79])).
% 56.42/45.39  tff(c_155064, plain, (![A_1524, A_1525]: (k2_pre_topc(A_1524, A_1525)=A_1525 | ~v4_pre_topc(A_1525, A_1524) | ~l1_pre_topc(A_1524) | ~r1_tarski(A_1525, u1_struct_0(A_1524)))), inference(resolution, [status(thm)], [c_22, c_151044])).
% 56.42/45.39  tff(c_172965, plain, (![A_1666, B_1667]: (k2_pre_topc(A_1666, k4_xboole_0(u1_struct_0(A_1666), B_1667))=k4_xboole_0(u1_struct_0(A_1666), B_1667) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(A_1666), B_1667), A_1666) | ~l1_pre_topc(A_1666))), inference(resolution, [status(thm)], [c_10, c_155064])).
% 56.42/45.39  tff(c_173005, plain, (k2_pre_topc('#skF_1', k4_xboole_0(u1_struct_0('#skF_1'), '#skF_3'))=k4_xboole_0(u1_struct_0('#skF_1'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_150442, c_172965])).
% 56.42/45.39  tff(c_173032, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_150442, c_150442, c_173005])).
% 56.42/45.39  tff(c_173442, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_173032])).
% 56.42/45.39  tff(c_145880, plain, (![A_1337, B_1338]: (m1_subset_1(k2_pre_topc(A_1337, B_1338), k1_zfmisc_1(u1_struct_0(A_1337))) | ~m1_subset_1(B_1338, k1_zfmisc_1(u1_struct_0(A_1337))) | ~l1_pre_topc(A_1337))), inference(cnfTransformation, [status(thm)], [f_57])).
% 56.42/45.39  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 56.42/45.39  tff(c_150039, plain, (![A_1411, B_1412]: (r1_tarski(k2_pre_topc(A_1411, B_1412), u1_struct_0(A_1411)) | ~m1_subset_1(B_1412, k1_zfmisc_1(u1_struct_0(A_1411))) | ~l1_pre_topc(A_1411))), inference(resolution, [status(thm)], [c_145880, c_20])).
% 56.42/45.39  tff(c_64, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.42/45.39  tff(c_144872, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 56.42/45.39  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.42/45.39  tff(c_72, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.42/45.39  tff(c_109, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_72])).
% 56.42/45.39  tff(c_147183, plain, (![A_1364, B_1365]: (k1_tops_1(A_1364, k2_pre_topc(A_1364, B_1365))=B_1365 | ~v6_tops_1(B_1365, A_1364) | ~m1_subset_1(B_1365, k1_zfmisc_1(u1_struct_0(A_1364))) | ~l1_pre_topc(A_1364))), inference(cnfTransformation, [status(thm)], [f_106])).
% 56.42/45.39  tff(c_147192, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_147183])).
% 56.42/45.39  tff(c_147200, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_109, c_147192])).
% 56.42/45.39  tff(c_145612, plain, (![A_1331, B_1332]: (v3_pre_topc(k1_tops_1(A_1331, B_1332), A_1331) | ~m1_subset_1(B_1332, k1_zfmisc_1(u1_struct_0(A_1331))) | ~l1_pre_topc(A_1331) | ~v2_pre_topc(A_1331))), inference(cnfTransformation, [status(thm)], [f_114])).
% 56.42/45.39  tff(c_150020, plain, (![A_1409, A_1410]: (v3_pre_topc(k1_tops_1(A_1409, A_1410), A_1409) | ~l1_pre_topc(A_1409) | ~v2_pre_topc(A_1409) | ~r1_tarski(A_1410, u1_struct_0(A_1409)))), inference(resolution, [status(thm)], [c_22, c_145612])).
% 56.42/45.39  tff(c_150023, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_147200, c_150020])).
% 56.42/45.39  tff(c_150028, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_150023])).
% 56.42/45.39  tff(c_150029, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_144872, c_150028])).
% 56.42/45.39  tff(c_150042, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_150039, c_150029])).
% 56.42/45.39  tff(c_150054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_150042])).
% 56.42/45.39  tff(c_150056, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 56.42/45.39  tff(c_46, plain, (![B_38, A_36]: (v4_pre_topc(B_38, A_36) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_36), B_38), A_36) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_123])).
% 56.42/45.39  tff(c_152113, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_151953, c_46])).
% 56.42/45.39  tff(c_152117, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_150056, c_152113])).
% 56.42/45.39  tff(c_208953, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_173442, c_152117])).
% 56.42/45.39  tff(c_208956, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_208953])).
% 56.42/45.39  tff(c_208960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150481, c_208956])).
% 56.42/45.39  tff(c_208961, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_173032])).
% 56.42/45.39  tff(c_32, plain, (![A_25, B_27]: (k3_subset_1(u1_struct_0(A_25), k2_pre_topc(A_25, k3_subset_1(u1_struct_0(A_25), B_27)))=k1_tops_1(A_25, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_86])).
% 56.42/45.39  tff(c_209012, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_208961, c_32])).
% 56.42/45.39  tff(c_209052, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_151953, c_209012])).
% 56.42/45.39  tff(c_68, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.42/45.39  tff(c_110, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_68])).
% 56.42/45.39  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.42/45.39  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.42/45.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 56.42/45.39  tff(c_49070, plain, (![B_581, A_582]: (r1_tarski(B_581, k2_pre_topc(A_582, B_581)) | ~m1_subset_1(B_581, k1_zfmisc_1(u1_struct_0(A_582))) | ~l1_pre_topc(A_582))), inference(cnfTransformation, [status(thm)], [f_64])).
% 56.42/45.39  tff(c_49075, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_49070])).
% 56.42/45.39  tff(c_49081, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_49075])).
% 56.42/45.39  tff(c_5729, plain, (![B_202, A_203]: (r1_tarski(B_202, k2_pre_topc(A_203, B_202)) | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_64])).
% 56.42/45.39  tff(c_5736, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_5729])).
% 56.42/45.39  tff(c_5743, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5736])).
% 56.42/45.39  tff(c_146, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 56.42/45.39  tff(c_158, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_146])).
% 56.42/45.39  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 56.42/45.39  tff(c_5414, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_158, c_8])).
% 56.42/45.39  tff(c_131, plain, (![A_67, B_68]: (k1_setfam_1(k2_tarski(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_47])).
% 56.42/45.39  tff(c_5426, plain, (![B_184, A_185]: (k1_setfam_1(k2_tarski(B_184, A_185))=k3_xboole_0(A_185, B_184))), inference(superposition, [status(thm), theory('equality')], [c_14, c_131])).
% 56.42/45.39  tff(c_5432, plain, (![B_184, A_185]: (k3_xboole_0(B_184, A_185)=k3_xboole_0(A_185, B_184))), inference(superposition, [status(thm), theory('equality')], [c_5426, c_18])).
% 56.42/45.39  tff(c_5575, plain, (![A_196, B_197]: (k4_xboole_0(A_196, B_197)=k3_subset_1(A_196, B_197) | ~m1_subset_1(B_197, k1_zfmisc_1(A_196)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 56.42/45.39  tff(c_5587, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_54, c_5575])).
% 56.42/45.39  tff(c_5610, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_xboole_0(u1_struct_0('#skF_1'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5587, c_12])).
% 56.42/45.39  tff(c_5616, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5414, c_5432, c_5610])).
% 56.42/45.39  tff(c_5613, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5587, c_10])).
% 56.42/45.39  tff(c_7308, plain, (![B_236, A_237]: (k4_xboole_0(B_236, A_237)=k3_subset_1(B_236, A_237) | ~r1_tarski(A_237, B_236))), inference(resolution, [status(thm)], [c_22, c_5575])).
% 56.42/45.39  tff(c_7320, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(resolution, [status(thm)], [c_5613, c_7308])).
% 56.42/45.39  tff(c_7346, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5616, c_7320])).
% 56.42/45.39  tff(c_6261, plain, (![A_216, B_217]: (k2_pre_topc(A_216, B_217)=B_217 | ~v4_pre_topc(B_217, A_216) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216))), inference(cnfTransformation, [status(thm)], [f_79])).
% 56.42/45.39  tff(c_9929, plain, (![A_284, A_285]: (k2_pre_topc(A_284, A_285)=A_285 | ~v4_pre_topc(A_285, A_284) | ~l1_pre_topc(A_284) | ~r1_tarski(A_285, u1_struct_0(A_284)))), inference(resolution, [status(thm)], [c_22, c_6261])).
% 56.42/45.39  tff(c_29418, plain, (![A_438, B_439]: (k2_pre_topc(A_438, k4_xboole_0(u1_struct_0(A_438), B_439))=k4_xboole_0(u1_struct_0(A_438), B_439) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(A_438), B_439), A_438) | ~l1_pre_topc(A_438))), inference(resolution, [status(thm)], [c_10, c_9929])).
% 56.42/45.39  tff(c_29458, plain, (k2_pre_topc('#skF_1', k4_xboole_0(u1_struct_0('#skF_1'), '#skF_3'))=k4_xboole_0(u1_struct_0('#skF_1'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5587, c_29418])).
% 56.42/45.39  tff(c_29485, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5587, c_5587, c_29458])).
% 56.42/45.39  tff(c_29492, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_29485])).
% 56.42/45.39  tff(c_1016, plain, (![A_103, B_104]: (m1_subset_1(k2_pre_topc(A_103, B_104), k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_57])).
% 56.42/45.39  tff(c_1031, plain, (![A_103, B_104]: (r1_tarski(k2_pre_topc(A_103, B_104), u1_struct_0(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_1016, c_20])).
% 56.42/45.39  tff(c_163, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 56.42/45.39  tff(c_1596, plain, (![A_113, B_114]: (k1_tops_1(A_113, k2_pre_topc(A_113, B_114))=B_114 | ~v6_tops_1(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_106])).
% 56.42/45.39  tff(c_1605, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_1596])).
% 56.42/45.39  tff(c_1613, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_109, c_1605])).
% 56.42/45.39  tff(c_1142, plain, (![A_105, B_106]: (v3_pre_topc(k1_tops_1(A_105, B_106), A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_114])).
% 56.42/45.39  tff(c_5395, plain, (![A_182, A_183]: (v3_pre_topc(k1_tops_1(A_182, A_183), A_182) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | ~r1_tarski(A_183, u1_struct_0(A_182)))), inference(resolution, [status(thm)], [c_22, c_1142])).
% 56.42/45.39  tff(c_5398, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1613, c_5395])).
% 56.42/45.39  tff(c_5400, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5398])).
% 56.42/45.39  tff(c_5401, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_163, c_5400])).
% 56.42/45.39  tff(c_5404, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1031, c_5401])).
% 56.42/45.39  tff(c_5408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_5404])).
% 56.42/45.39  tff(c_5410, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 56.42/45.39  tff(c_7520, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7346, c_46])).
% 56.42/45.39  tff(c_7526, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5410, c_7520])).
% 56.42/45.39  tff(c_48722, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_29492, c_7526])).
% 56.42/45.39  tff(c_48725, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_48722])).
% 56.42/45.39  tff(c_48729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5613, c_48725])).
% 56.42/45.39  tff(c_48730, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_29485])).
% 56.42/45.39  tff(c_48776, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_48730, c_32])).
% 56.42/45.39  tff(c_48816, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_7346, c_48776])).
% 56.42/45.39  tff(c_5409, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 56.42/45.39  tff(c_5425, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_5409])).
% 56.42/45.39  tff(c_7851, plain, (![A_250, B_251]: (k1_tops_1(A_250, k2_pre_topc(A_250, B_251))=B_251 | ~v6_tops_1(B_251, A_250) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_250))) | ~l1_pre_topc(A_250))), inference(cnfTransformation, [status(thm)], [f_106])).
% 56.42/45.39  tff(c_7860, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_7851])).
% 56.42/45.39  tff(c_7868, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_109, c_7860])).
% 56.42/45.39  tff(c_8988, plain, (![B_274, A_275]: (v4_tops_1(B_274, A_275) | ~r1_tarski(B_274, k2_pre_topc(A_275, k1_tops_1(A_275, B_274))) | ~r1_tarski(k1_tops_1(A_275, k2_pre_topc(A_275, B_274)), B_274) | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0(A_275))) | ~l1_pre_topc(A_275))), inference(cnfTransformation, [status(thm)], [f_97])).
% 56.42/45.39  tff(c_8998, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7868, c_8988])).
% 56.42/45.39  tff(c_9002, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_6, c_8998])).
% 56.42/45.39  tff(c_9003, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_5425, c_9002])).
% 56.42/45.39  tff(c_48826, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48816, c_9003])).
% 56.42/45.39  tff(c_48832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5743, c_48826])).
% 56.42/45.39  tff(c_48833, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_5409])).
% 56.42/45.39  tff(c_48835, plain, (![A_565, B_566]: (k1_setfam_1(k2_tarski(A_565, B_566))=k3_xboole_0(B_566, A_565))), inference(superposition, [status(thm), theory('equality')], [c_14, c_131])).
% 56.42/45.39  tff(c_48841, plain, (![B_566, A_565]: (k3_xboole_0(B_566, A_565)=k3_xboole_0(A_565, B_566))), inference(superposition, [status(thm), theory('equality')], [c_48835, c_18])).
% 56.42/45.39  tff(c_51441, plain, (![A_633, B_634]: (r1_tarski(k1_tops_1(A_633, k2_pre_topc(A_633, B_634)), B_634) | ~v4_tops_1(B_634, A_633) | ~m1_subset_1(B_634, k1_zfmisc_1(u1_struct_0(A_633))) | ~l1_pre_topc(A_633))), inference(cnfTransformation, [status(thm)], [f_97])).
% 56.42/45.39  tff(c_51449, plain, (![A_633, B_634]: (k3_xboole_0(k1_tops_1(A_633, k2_pre_topc(A_633, B_634)), B_634)=k1_tops_1(A_633, k2_pre_topc(A_633, B_634)) | ~v4_tops_1(B_634, A_633) | ~m1_subset_1(B_634, k1_zfmisc_1(u1_struct_0(A_633))) | ~l1_pre_topc(A_633))), inference(resolution, [status(thm)], [c_51441, c_8])).
% 56.42/45.39  tff(c_141438, plain, (![B_1279, A_1280]: (k3_xboole_0(B_1279, k1_tops_1(A_1280, k2_pre_topc(A_1280, B_1279)))=k1_tops_1(A_1280, k2_pre_topc(A_1280, B_1279)) | ~v4_tops_1(B_1279, A_1280) | ~m1_subset_1(B_1279, k1_zfmisc_1(u1_struct_0(A_1280))) | ~l1_pre_topc(A_1280))), inference(demodulation, [status(thm), theory('equality')], [c_48841, c_51449])).
% 56.42/45.39  tff(c_141447, plain, (k3_xboole_0('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')) | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_141438])).
% 56.42/45.39  tff(c_141457, plain, (k3_xboole_0('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48833, c_141447])).
% 56.42/45.39  tff(c_49553, plain, (![A_595, B_596]: (m1_subset_1(k2_pre_topc(A_595, B_596), k1_zfmisc_1(u1_struct_0(A_595))) | ~m1_subset_1(B_596, k1_zfmisc_1(u1_struct_0(A_595))) | ~l1_pre_topc(A_595))), inference(cnfTransformation, [status(thm)], [f_57])).
% 56.42/45.39  tff(c_53724, plain, (![A_669, B_670]: (r1_tarski(k2_pre_topc(A_669, B_670), u1_struct_0(A_669)) | ~m1_subset_1(B_670, k1_zfmisc_1(u1_struct_0(A_669))) | ~l1_pre_topc(A_669))), inference(resolution, [status(thm)], [c_49553, c_20])).
% 56.42/45.39  tff(c_53732, plain, (![A_669, B_670]: (k3_xboole_0(k2_pre_topc(A_669, B_670), u1_struct_0(A_669))=k2_pre_topc(A_669, B_670) | ~m1_subset_1(B_670, k1_zfmisc_1(u1_struct_0(A_669))) | ~l1_pre_topc(A_669))), inference(resolution, [status(thm)], [c_53724, c_8])).
% 56.42/45.39  tff(c_119692, plain, (![A_1125, B_1126]: (k3_xboole_0(u1_struct_0(A_1125), k2_pre_topc(A_1125, B_1126))=k2_pre_topc(A_1125, B_1126) | ~m1_subset_1(B_1126, k1_zfmisc_1(u1_struct_0(A_1125))) | ~l1_pre_topc(A_1125))), inference(demodulation, [status(thm), theory('equality')], [c_48841, c_53732])).
% 56.42/45.39  tff(c_119701, plain, (k3_xboole_0(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k2_pre_topc('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_119692])).
% 56.42/45.39  tff(c_119711, plain, (k3_xboole_0(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_119701])).
% 56.42/45.39  tff(c_48912, plain, (![A_571, B_572]: (k4_xboole_0(A_571, k4_xboole_0(A_571, B_572))=k3_xboole_0(A_571, B_572))), inference(cnfTransformation, [status(thm)], [f_39])).
% 56.42/45.39  tff(c_48921, plain, (![A_571, B_572]: (r1_tarski(k3_xboole_0(A_571, B_572), A_571))), inference(superposition, [status(thm), theory('equality')], [c_48912, c_10])).
% 56.42/45.39  tff(c_119948, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_119711, c_48921])).
% 56.42/45.39  tff(c_157, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_146])).
% 56.42/45.39  tff(c_162, plain, (k3_xboole_0('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_157, c_8])).
% 56.42/45.39  tff(c_48984, plain, (![A_577, B_578]: (k4_xboole_0(A_577, B_578)=k3_subset_1(A_577, B_578) | ~m1_subset_1(B_578, k1_zfmisc_1(A_577)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 56.42/45.39  tff(c_48995, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_4')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_52, c_48984])).
% 56.42/45.39  tff(c_49039, plain, (k4_xboole_0(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_xboole_0(u1_struct_0('#skF_2'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48995, c_12])).
% 56.42/45.39  tff(c_49046, plain, (k4_xboole_0(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_48841, c_49039])).
% 56.42/45.39  tff(c_49042, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_48995, c_10])).
% 56.42/45.39  tff(c_50712, plain, (![B_613, A_614]: (k4_xboole_0(B_613, A_614)=k3_subset_1(B_613, A_614) | ~r1_tarski(A_614, B_613))), inference(resolution, [status(thm)], [c_22, c_48984])).
% 56.42/45.39  tff(c_50727, plain, (k4_xboole_0(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(resolution, [status(thm)], [c_49042, c_50712])).
% 56.42/45.39  tff(c_50752, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_49046, c_50727])).
% 56.42/45.39  tff(c_49798, plain, (![A_599, B_600]: (k2_pre_topc(A_599, B_600)=B_600 | ~v4_pre_topc(B_600, A_599) | ~m1_subset_1(B_600, k1_zfmisc_1(u1_struct_0(A_599))) | ~l1_pre_topc(A_599))), inference(cnfTransformation, [status(thm)], [f_79])).
% 56.42/45.39  tff(c_53746, plain, (![A_671, A_672]: (k2_pre_topc(A_671, A_672)=A_672 | ~v4_pre_topc(A_672, A_671) | ~l1_pre_topc(A_671) | ~r1_tarski(A_672, u1_struct_0(A_671)))), inference(resolution, [status(thm)], [c_22, c_49798])).
% 56.42/45.39  tff(c_123415, plain, (![A_1138, B_1139]: (k2_pre_topc(A_1138, k4_xboole_0(u1_struct_0(A_1138), B_1139))=k4_xboole_0(u1_struct_0(A_1138), B_1139) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(A_1138), B_1139), A_1138) | ~l1_pre_topc(A_1138))), inference(resolution, [status(thm)], [c_10, c_53746])).
% 56.42/45.39  tff(c_123455, plain, (k2_pre_topc('#skF_2', k4_xboole_0(u1_struct_0('#skF_2'), '#skF_4'))=k4_xboole_0(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_48995, c_123415])).
% 56.42/45.39  tff(c_123480, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48995, c_48995, c_123455])).
% 56.42/45.39  tff(c_124420, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_123480])).
% 56.42/45.39  tff(c_48834, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_5409])).
% 56.42/45.39  tff(c_66, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.42/45.39  tff(c_48892, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5410, c_48834, c_66])).
% 56.42/45.39  tff(c_51242, plain, (![B_629, A_630]: (v4_pre_topc(B_629, A_630) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_630), B_629), A_630) | ~m1_subset_1(B_629, k1_zfmisc_1(u1_struct_0(A_630))) | ~l1_pre_topc(A_630))), inference(cnfTransformation, [status(thm)], [f_123])).
% 56.42/45.39  tff(c_51245, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50752, c_51242])).
% 56.42/45.39  tff(c_51265, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48892, c_51245])).
% 56.42/45.39  tff(c_138304, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_124420, c_51265])).
% 56.42/45.39  tff(c_138307, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_138304])).
% 56.42/45.39  tff(c_138311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49042, c_138307])).
% 56.42/45.39  tff(c_138312, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_123480])).
% 56.42/45.39  tff(c_138442, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_138312, c_32])).
% 56.42/45.39  tff(c_138482, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50752, c_138442])).
% 56.42/45.39  tff(c_52051, plain, (![A_647, B_648, C_649]: (r1_tarski(k1_tops_1(A_647, B_648), k1_tops_1(A_647, C_649)) | ~r1_tarski(B_648, C_649) | ~m1_subset_1(C_649, k1_zfmisc_1(u1_struct_0(A_647))) | ~m1_subset_1(B_648, k1_zfmisc_1(u1_struct_0(A_647))) | ~l1_pre_topc(A_647))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.42/45.39  tff(c_109045, plain, (![A_1048, B_1049, C_1050]: (k3_xboole_0(k1_tops_1(A_1048, B_1049), k1_tops_1(A_1048, C_1050))=k1_tops_1(A_1048, B_1049) | ~r1_tarski(B_1049, C_1050) | ~m1_subset_1(C_1050, k1_zfmisc_1(u1_struct_0(A_1048))) | ~m1_subset_1(B_1049, k1_zfmisc_1(u1_struct_0(A_1048))) | ~l1_pre_topc(A_1048))), inference(resolution, [status(thm)], [c_52051, c_8])).
% 56.42/45.39  tff(c_144652, plain, (![A_1290, B_1291, A_1292]: (k3_xboole_0(k1_tops_1(A_1290, B_1291), k1_tops_1(A_1290, A_1292))=k1_tops_1(A_1290, B_1291) | ~r1_tarski(B_1291, A_1292) | ~m1_subset_1(B_1291, k1_zfmisc_1(u1_struct_0(A_1290))) | ~l1_pre_topc(A_1290) | ~r1_tarski(A_1292, u1_struct_0(A_1290)))), inference(resolution, [status(thm)], [c_22, c_109045])).
% 56.42/45.39  tff(c_144661, plain, (![A_1292]: (k3_xboole_0(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', A_1292))=k1_tops_1('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', A_1292) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_1292, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_52, c_144652])).
% 56.42/45.39  tff(c_144678, plain, (![A_1293]: (k3_xboole_0('#skF_4', k1_tops_1('#skF_2', A_1293))='#skF_4' | ~r1_tarski('#skF_4', A_1293) | ~r1_tarski(A_1293, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_138482, c_138482, c_144661])).
% 56.42/45.39  tff(c_144681, plain, (k3_xboole_0('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))='#skF_4' | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_119948, c_144678])).
% 56.42/45.39  tff(c_144721, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_49081, c_141457, c_144681])).
% 56.42/45.39  tff(c_48930, plain, (![A_573, B_574]: (r1_tarski(k3_xboole_0(A_573, B_574), A_573))), inference(superposition, [status(thm), theory('equality')], [c_48912, c_10])).
% 56.42/45.39  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 56.42/45.39  tff(c_48951, plain, (![A_573, B_574]: (k3_xboole_0(A_573, B_574)=A_573 | ~r1_tarski(A_573, k3_xboole_0(A_573, B_574)))), inference(resolution, [status(thm)], [c_48930, c_2])).
% 56.42/45.39  tff(c_141704, plain, (k3_xboole_0('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_141457, c_48951])).
% 56.42/45.39  tff(c_141837, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_141457, c_141704])).
% 56.42/45.39  tff(c_144647, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(splitLeft, [status(thm)], [c_141837])).
% 56.42/45.39  tff(c_144738, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_144721, c_144647])).
% 56.42/45.39  tff(c_144748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_144738])).
% 56.42/45.39  tff(c_144749, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_141837])).
% 56.42/45.39  tff(c_40, plain, (![B_33, A_31]: (v6_tops_1(B_33, A_31) | k1_tops_1(A_31, k2_pre_topc(A_31, B_33))!=B_33 | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_106])).
% 56.42/45.39  tff(c_144808, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_144749, c_40])).
% 56.42/45.39  tff(c_144841, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_144808])).
% 56.42/45.39  tff(c_144843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_144841])).
% 56.42/45.39  tff(c_144845, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_68])).
% 56.42/45.39  tff(c_62, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.42/45.39  tff(c_150059, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_150056, c_144845, c_62])).
% 56.42/45.39  tff(c_152499, plain, (![A_1482, B_1483]: (k1_tops_1(A_1482, k2_pre_topc(A_1482, B_1483))=B_1483 | ~v6_tops_1(B_1483, A_1482) | ~m1_subset_1(B_1483, k1_zfmisc_1(u1_struct_0(A_1482))) | ~l1_pre_topc(A_1482))), inference(cnfTransformation, [status(thm)], [f_106])).
% 56.42/45.39  tff(c_152508, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_152499])).
% 56.42/45.39  tff(c_152516, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_109, c_152508])).
% 56.42/45.39  tff(c_153811, plain, (![B_1510, A_1511]: (v4_tops_1(B_1510, A_1511) | ~r1_tarski(B_1510, k2_pre_topc(A_1511, k1_tops_1(A_1511, B_1510))) | ~r1_tarski(k1_tops_1(A_1511, k2_pre_topc(A_1511, B_1510)), B_1510) | ~m1_subset_1(B_1510, k1_zfmisc_1(u1_struct_0(A_1511))) | ~l1_pre_topc(A_1511))), inference(cnfTransformation, [status(thm)], [f_97])).
% 56.42/45.39  tff(c_153821, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_152516, c_153811])).
% 56.42/45.39  tff(c_153828, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_6, c_153821])).
% 56.42/45.39  tff(c_153829, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_150059, c_153828])).
% 56.42/45.39  tff(c_209061, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_209052, c_153829])).
% 56.42/45.39  tff(c_209066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150552, c_209061])).
% 56.42/45.39  tff(c_209068, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 56.42/45.39  tff(c_209070, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_209068, c_68])).
% 56.42/45.39  tff(c_209527, plain, (![B_1888, A_1889]: (r1_tarski(B_1888, k2_pre_topc(A_1889, B_1888)) | ~m1_subset_1(B_1888, k1_zfmisc_1(u1_struct_0(A_1889))) | ~l1_pre_topc(A_1889))), inference(cnfTransformation, [status(thm)], [f_64])).
% 56.42/45.39  tff(c_209532, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_209527])).
% 56.42/45.39  tff(c_209538, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_209532])).
% 56.42/45.39  tff(c_70, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.42/45.39  tff(c_209069, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_209068, c_70])).
% 56.42/45.39  tff(c_209071, plain, (![A_1859, B_1860]: (k1_setfam_1(k2_tarski(A_1859, B_1860))=k3_xboole_0(A_1859, B_1860))), inference(cnfTransformation, [status(thm)], [f_47])).
% 56.42/45.39  tff(c_209171, plain, (![B_1872, A_1873]: (k1_setfam_1(k2_tarski(B_1872, A_1873))=k3_xboole_0(A_1873, B_1872))), inference(superposition, [status(thm), theory('equality')], [c_14, c_209071])).
% 56.42/45.39  tff(c_209177, plain, (![B_1872, A_1873]: (k3_xboole_0(B_1872, A_1873)=k3_xboole_0(A_1873, B_1872))), inference(superposition, [status(thm), theory('equality')], [c_209171, c_18])).
% 56.42/45.39  tff(c_211986, plain, (![A_1940, B_1941]: (r1_tarski(k1_tops_1(A_1940, k2_pre_topc(A_1940, B_1941)), B_1941) | ~v4_tops_1(B_1941, A_1940) | ~m1_subset_1(B_1941, k1_zfmisc_1(u1_struct_0(A_1940))) | ~l1_pre_topc(A_1940))), inference(cnfTransformation, [status(thm)], [f_97])).
% 56.42/45.39  tff(c_211994, plain, (![A_1940, B_1941]: (k3_xboole_0(k1_tops_1(A_1940, k2_pre_topc(A_1940, B_1941)), B_1941)=k1_tops_1(A_1940, k2_pre_topc(A_1940, B_1941)) | ~v4_tops_1(B_1941, A_1940) | ~m1_subset_1(B_1941, k1_zfmisc_1(u1_struct_0(A_1940))) | ~l1_pre_topc(A_1940))), inference(resolution, [status(thm)], [c_211986, c_8])).
% 56.42/45.39  tff(c_248176, plain, (![B_2234, A_2235]: (k3_xboole_0(B_2234, k1_tops_1(A_2235, k2_pre_topc(A_2235, B_2234)))=k1_tops_1(A_2235, k2_pre_topc(A_2235, B_2234)) | ~v4_tops_1(B_2234, A_2235) | ~m1_subset_1(B_2234, k1_zfmisc_1(u1_struct_0(A_2235))) | ~l1_pre_topc(A_2235))), inference(demodulation, [status(thm), theory('equality')], [c_209177, c_211994])).
% 56.42/45.39  tff(c_248183, plain, (k3_xboole_0('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')) | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_248176])).
% 56.42/45.39  tff(c_248190, plain, (k3_xboole_0('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_209069, c_248183])).
% 56.42/45.39  tff(c_210102, plain, (![A_1902, B_1903]: (m1_subset_1(k2_pre_topc(A_1902, B_1903), k1_zfmisc_1(u1_struct_0(A_1902))) | ~m1_subset_1(B_1903, k1_zfmisc_1(u1_struct_0(A_1902))) | ~l1_pre_topc(A_1902))), inference(cnfTransformation, [status(thm)], [f_57])).
% 56.42/45.39  tff(c_213590, plain, (![A_1968, B_1969]: (r1_tarski(k2_pre_topc(A_1968, B_1969), u1_struct_0(A_1968)) | ~m1_subset_1(B_1969, k1_zfmisc_1(u1_struct_0(A_1968))) | ~l1_pre_topc(A_1968))), inference(resolution, [status(thm)], [c_210102, c_20])).
% 56.42/45.39  tff(c_213598, plain, (![A_1968, B_1969]: (k3_xboole_0(k2_pre_topc(A_1968, B_1969), u1_struct_0(A_1968))=k2_pre_topc(A_1968, B_1969) | ~m1_subset_1(B_1969, k1_zfmisc_1(u1_struct_0(A_1968))) | ~l1_pre_topc(A_1968))), inference(resolution, [status(thm)], [c_213590, c_8])).
% 56.42/45.39  tff(c_227186, plain, (![A_2098, B_2099]: (k3_xboole_0(u1_struct_0(A_2098), k2_pre_topc(A_2098, B_2099))=k2_pre_topc(A_2098, B_2099) | ~m1_subset_1(B_2099, k1_zfmisc_1(u1_struct_0(A_2098))) | ~l1_pre_topc(A_2098))), inference(demodulation, [status(thm), theory('equality')], [c_209177, c_213598])).
% 56.42/45.39  tff(c_227193, plain, (k3_xboole_0(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k2_pre_topc('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_227186])).
% 56.42/45.39  tff(c_227200, plain, (k3_xboole_0(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_227193])).
% 56.42/45.39  tff(c_209127, plain, (![A_1868, B_1869]: (k4_xboole_0(A_1868, k4_xboole_0(A_1868, B_1869))=k3_xboole_0(A_1868, B_1869))), inference(cnfTransformation, [status(thm)], [f_39])).
% 56.42/45.39  tff(c_209136, plain, (![A_1868, B_1869]: (r1_tarski(k3_xboole_0(A_1868, B_1869), A_1868))), inference(superposition, [status(thm), theory('equality')], [c_209127, c_10])).
% 56.42/45.39  tff(c_227443, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_227200, c_209136])).
% 56.42/45.39  tff(c_209106, plain, (![A_1866, B_1867]: (r1_tarski(A_1866, B_1867) | ~m1_subset_1(A_1866, k1_zfmisc_1(B_1867)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 56.42/45.39  tff(c_209117, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_209106])).
% 56.42/45.39  tff(c_209122, plain, (k3_xboole_0('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_209117, c_8])).
% 56.42/45.39  tff(c_209435, plain, (![A_1886, B_1887]: (k4_xboole_0(A_1886, B_1887)=k3_subset_1(A_1886, B_1887) | ~m1_subset_1(B_1887, k1_zfmisc_1(A_1886)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 56.42/45.39  tff(c_209446, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_4')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_52, c_209435])).
% 56.42/45.39  tff(c_211029, plain, (![B_1916, A_1917]: (k4_xboole_0(B_1916, A_1917)=k3_subset_1(B_1916, A_1917) | ~r1_tarski(A_1917, B_1916))), inference(resolution, [status(thm)], [c_22, c_209435])).
% 56.42/45.39  tff(c_211059, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_subset_1(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_211029])).
% 56.42/45.39  tff(c_211140, plain, (![A_1921, B_1922]: (k3_subset_1(A_1921, k4_xboole_0(A_1921, B_1922))=k3_xboole_0(A_1921, B_1922))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_211059])).
% 56.42/45.39  tff(c_211164, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_xboole_0(u1_struct_0('#skF_2'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_209446, c_211140])).
% 56.42/45.39  tff(c_211172, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_209122, c_209177, c_211164])).
% 56.42/45.39  tff(c_209457, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_209446, c_10])).
% 56.42/45.39  tff(c_209975, plain, (![A_1900, B_1901]: (k2_pre_topc(A_1900, B_1901)=B_1901 | ~v4_pre_topc(B_1901, A_1900) | ~m1_subset_1(B_1901, k1_zfmisc_1(u1_struct_0(A_1900))) | ~l1_pre_topc(A_1900))), inference(cnfTransformation, [status(thm)], [f_79])).
% 56.42/45.39  tff(c_214000, plain, (![A_1974, A_1975]: (k2_pre_topc(A_1974, A_1975)=A_1975 | ~v4_pre_topc(A_1975, A_1974) | ~l1_pre_topc(A_1974) | ~r1_tarski(A_1975, u1_struct_0(A_1974)))), inference(resolution, [status(thm)], [c_22, c_209975])).
% 56.42/45.39  tff(c_230859, plain, (![A_2108, B_2109]: (k2_pre_topc(A_2108, k4_xboole_0(u1_struct_0(A_2108), B_2109))=k4_xboole_0(u1_struct_0(A_2108), B_2109) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(A_2108), B_2109), A_2108) | ~l1_pre_topc(A_2108))), inference(resolution, [status(thm)], [c_10, c_214000])).
% 56.42/45.39  tff(c_230899, plain, (k2_pre_topc('#skF_2', k4_xboole_0(u1_struct_0('#skF_2'), '#skF_4'))=k4_xboole_0(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_209446, c_230859])).
% 56.42/45.39  tff(c_230925, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_209446, c_209446, c_230899])).
% 56.42/45.39  tff(c_231382, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_230925])).
% 56.42/45.39  tff(c_209067, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_72])).
% 56.42/45.39  tff(c_211794, plain, (![B_1936, A_1937]: (v4_pre_topc(B_1936, A_1937) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_1937), B_1936), A_1937) | ~m1_subset_1(B_1936, k1_zfmisc_1(u1_struct_0(A_1937))) | ~l1_pre_topc(A_1937))), inference(cnfTransformation, [status(thm)], [f_123])).
% 56.42/45.39  tff(c_211807, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_211172, c_211794])).
% 56.42/45.39  tff(c_211824, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_209067, c_211807])).
% 56.42/45.39  tff(c_243282, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_231382, c_211824])).
% 56.42/45.39  tff(c_243285, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_243282])).
% 56.42/45.39  tff(c_243289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209457, c_243285])).
% 56.42/45.39  tff(c_243290, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_230925])).
% 56.42/45.39  tff(c_243333, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_243290, c_32])).
% 56.42/45.39  tff(c_243371, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_211172, c_243333])).
% 56.42/45.39  tff(c_212572, plain, (![A_1955, B_1956, C_1957]: (r1_tarski(k1_tops_1(A_1955, B_1956), k1_tops_1(A_1955, C_1957)) | ~r1_tarski(B_1956, C_1957) | ~m1_subset_1(C_1957, k1_zfmisc_1(u1_struct_0(A_1955))) | ~m1_subset_1(B_1956, k1_zfmisc_1(u1_struct_0(A_1955))) | ~l1_pre_topc(A_1955))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.42/45.39  tff(c_217736, plain, (![A_2024, B_2025, C_2026]: (k3_xboole_0(k1_tops_1(A_2024, B_2025), k1_tops_1(A_2024, C_2026))=k1_tops_1(A_2024, B_2025) | ~r1_tarski(B_2025, C_2026) | ~m1_subset_1(C_2026, k1_zfmisc_1(u1_struct_0(A_2024))) | ~m1_subset_1(B_2025, k1_zfmisc_1(u1_struct_0(A_2024))) | ~l1_pre_topc(A_2024))), inference(resolution, [status(thm)], [c_212572, c_8])).
% 56.42/45.39  tff(c_249318, plain, (![A_2240, B_2241, A_2242]: (k3_xboole_0(k1_tops_1(A_2240, B_2241), k1_tops_1(A_2240, A_2242))=k1_tops_1(A_2240, B_2241) | ~r1_tarski(B_2241, A_2242) | ~m1_subset_1(B_2241, k1_zfmisc_1(u1_struct_0(A_2240))) | ~l1_pre_topc(A_2240) | ~r1_tarski(A_2242, u1_struct_0(A_2240)))), inference(resolution, [status(thm)], [c_22, c_217736])).
% 56.42/45.39  tff(c_249325, plain, (![A_2242]: (k3_xboole_0(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', A_2242))=k1_tops_1('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', A_2242) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_2242, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_52, c_249318])).
% 56.42/45.39  tff(c_249339, plain, (![A_2243]: (k3_xboole_0('#skF_4', k1_tops_1('#skF_2', A_2243))='#skF_4' | ~r1_tarski('#skF_4', A_2243) | ~r1_tarski(A_2243, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_243371, c_243371, c_249325])).
% 56.42/45.39  tff(c_249342, plain, (k3_xboole_0('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))='#skF_4' | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_227443, c_249339])).
% 56.42/45.39  tff(c_249382, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_209538, c_248190, c_249342])).
% 56.42/45.39  tff(c_249456, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_249382, c_40])).
% 56.42/45.39  tff(c_249489, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_249456])).
% 56.42/45.39  tff(c_249491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209070, c_249489])).
% 56.42/45.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.42/45.39  
% 56.42/45.39  Inference rules
% 56.42/45.39  ----------------------
% 56.42/45.39  #Ref     : 0
% 56.42/45.39  #Sup     : 60983
% 56.42/45.39  #Fact    : 0
% 56.42/45.39  #Define  : 0
% 56.42/45.39  #Split   : 173
% 56.42/45.39  #Chain   : 0
% 56.42/45.39  #Close   : 0
% 56.42/45.39  
% 56.42/45.39  Ordering : KBO
% 56.42/45.39  
% 56.42/45.39  Simplification rules
% 56.42/45.39  ----------------------
% 56.42/45.39  #Subsume      : 5566
% 56.42/45.39  #Demod        : 143658
% 56.42/45.39  #Tautology    : 37586
% 56.42/45.39  #SimpNegUnit  : 281
% 56.42/45.39  #BackRed      : 81
% 56.42/45.39  
% 56.42/45.39  #Partial instantiations: 0
% 56.42/45.39  #Strategies tried      : 1
% 56.42/45.39  
% 56.42/45.39  Timing (in seconds)
% 56.42/45.39  ----------------------
% 56.42/45.39  Preprocessing        : 0.37
% 56.42/45.39  Parsing              : 0.20
% 56.42/45.39  CNF conversion       : 0.03
% 56.42/45.39  Main loop            : 44.17
% 56.42/45.39  Inferencing          : 4.99
% 56.42/45.39  Reduction            : 29.60
% 56.42/45.39  Demodulation         : 27.06
% 56.42/45.39  BG Simplification    : 0.52
% 56.42/45.39  Subsumption          : 7.70
% 56.42/45.39  Abstraction          : 1.40
% 56.42/45.39  MUC search           : 0.00
% 56.42/45.39  Cooper               : 0.00
% 56.42/45.40  Total                : 44.63
% 56.42/45.40  Index Insertion      : 0.00
% 56.42/45.40  Index Deletion       : 0.00
% 56.42/45.40  Index Matching       : 0.00
% 56.42/45.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
